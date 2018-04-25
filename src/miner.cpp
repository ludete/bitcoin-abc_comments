// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "miner.h"

#include "amount.h"
#include "chain.h"
#include "chainparams.h"
#include "coins.h"
#include "config.h"
#include "consensus/consensus.h"
#include "consensus/merkle.h"
#include "consensus/validation.h"
#include "hash.h"
#include "net.h"
#include "policy/policy.h"
#include "pow.h"
#include "primitives/transaction.h"
#include "script/standard.h"
#include "timedata.h"
#include "txmempool.h"
#include "util.h"
#include "utilmoneystr.h"
#include "validation.h"
#include "validationinterface.h"

#include <algorithm>
#include <queue>
#include <utility>

#include <boost/thread.hpp>
#include <boost/tuple/tuple.hpp>

static const int MAX_COINBASE_SCRIPTSIG_SIZE = 100;

//////////////////////////////////////////////////////////////////////////////
//
// BitcoinMiner
//

//
// Unconfirmed transactions in the memory pool often depend on other
// transactions in the memory pool. When we select transactions from the
// pool, we select by highest priority or fee rate, so we might consider
// transactions that depend on transactions that aren't yet in the block.

uint64_t nLastBlockTx = 0;
uint64_t nLastBlockSize = 0;

class ScoreCompare {
public:
    ScoreCompare() {}

    bool operator()(const CTxMemPool::txiter a, const CTxMemPool::txiter b) {
        // Convert to less than.
        return CompareTxMemPoolEntryByScore()(*b, *a);
    }
};

//更新块的时间； pblock(out):要更新时间的块；consensusParams(in):当前运行主链的共识规则
//pindexPrev(in):要更新块的父块
int64_t UpdateTime(CBlockHeader *pblock,
                   const Consensus::Params &consensusParams,
                   const CBlockIndex *pindexPrev) {
    int64_t nOldTime = pblock->nTime;

    //1. 基于父块和当前时间，获取最大的时间戳。
    int64_t nNewTime =
        std::max(pindexPrev->GetMedianTimePast() + 1, GetAdjustedTime());

    //2. 更新块的时间戳
    if (nOldTime < nNewTime) {
        pblock->nTime = nNewTime;
    }

    // Updating time can change work required on testnet:
    //3. 更新区块的难度；只有测试链与回归测试链为true.
    if (consensusParams.fPowAllowMinDifficultyBlocks) {
        pblock->nBits =
            GetNextWorkRequired(pindexPrev, pblock, consensusParams);
    }

    //4. 返回两次的时间差
    return nNewTime - nOldTime;
}

//根据当前主链的运行参数，与主链的最高块，获取下个要挖块的最大容量。
static uint64_t ComputeMaxGeneratedBlockSize(const Config &config,
                                             const CBlockIndex *pindexPrev) {
    // Block resource limits
    // If -blockmaxsize is not given, limit to DEFAULT_MAX_GENERATED_BLOCK_SIZE
    // If only one is given, only restrict the specified resource.
    // If both are given, restrict both.
    //1. 默认为2M。
    uint64_t nMaxGeneratedBlockSize = DEFAULT_MAX_GENERATED_BLOCK_SIZE;
    //2. 如果手动指定，获取手动指定的大小
    if (IsArgSet("-blockmaxsize")) {
        nMaxGeneratedBlockSize =
            GetArg("-blockmaxsize", DEFAULT_MAX_GENERATED_BLOCK_SIZE);
    }

    // Limit size to between 1K and MaxBlockSize-1K for sanity:
    //3. 限制块的大小在 1K 到 8M-1000之间(当前的共识)
    nMaxGeneratedBlockSize =
        std::max(uint64_t(1000), std::min(config.GetMaxBlockSize() - 1000,
                                          nMaxGeneratedBlockSize));
    //4. 返回当前的要挖的块大小
    return nMaxGeneratedBlockSize;
}

BlockAssembler::BlockAssembler(const Config &_config,
                               const CChainParams &_chainparams)
    : chainparams(_chainparams), config(&_config) {
    if (IsArgSet("-blockmintxfee")) {
        Amount n = 0;
        ParseMoney(GetArg("-blockmintxfee", ""), n);
        blockMinFeeRate = CFeeRate(n);
    } else {
        blockMinFeeRate = CFeeRate(DEFAULT_BLOCK_MIN_TX_FEE);
    }

    LOCK(cs_main);
    nMaxGeneratedBlockSize =
        ComputeMaxGeneratedBlockSize(*config, chainActive.Tip());
}

//重置块模板
void BlockAssembler::resetBlock() {
    inBlock.clear();

    // Reserve space for coinbase tx. 为coinbase预留1000个字节，和100个操作码。
    nBlockSize = 1000;
    nBlockSigOps = 100;

    // These counters do not include coinbase tx.
    nBlockTx = 0;
    nFees = 0;

    lastFewTxs = 0;
    blockFinished = false;
}

static const std::vector<uint8_t>
getExcessiveBlockSizeSig(const Config &config) {
    std::string cbmsg = "/EB" + getSubVersionEB(config.GetMaxBlockSize()) + "/";
    const char *cbcstr = cbmsg.c_str();
    std::vector<uint8_t> vec(cbcstr, cbcstr + cbmsg.size());
    return vec;
}

//1. 生成一个新块。
std::unique_ptr<CBlockTemplate>
BlockAssembler::CreateNewBlock(const CScript &scriptPubKeyIn) {
    int64_t nTimeStart = GetTimeMicros();
    //1. 重置块模板
    resetBlock();

    //2. 创建块模板
    pblocktemplate.reset(new CBlockTemplate());
    if (!pblocktemplate.get()) {
        return nullptr;
    }

    // Pointer for convenience.
    //3. 将指针指向块模板
    pblock = &pblocktemplate->block;

    // Add dummy coinbase tx as first transaction.
    //4. 为coinbase预留交易集合，交易费，签名操作码数量的第一个位置。
    pblock->vtx.emplace_back();
    // updated at end
    pblocktemplate->vTxFees.push_back(-1);
    // updated at end
    pblocktemplate->vTxSigOpsCount.push_back(-1);

    //5. 设定当前块模板的高度。即当前主链的高度+1
    LOCK2(cs_main, mempool.cs);                     // 加锁。主锁和交易池的锁。
    CBlockIndex *pindexPrev = chainActive.Tip();
    nHeight = pindexPrev->nHeight + 1;

    //6. 获取当前的块版本号
    pblock->nVersion =
        ComputeBlockVersion(pindexPrev, chainparams.GetConsensus());
    // -regtest only: allow overriding block.nVersion with
    // -blockversion=N to test forking scenarios
    // 仅在回归测试的情况下，会进入，手动指定版本号
    if (chainparams.MineBlocksOnDemand()) {
        pblock->nVersion = GetArg("-blockversion", pblock->nVersion);
    }

    //7. 设置当前块的时间，最大容量
    pblock->nTime = GetAdjustedTime();
    nMaxGeneratedBlockSize = ComputeMaxGeneratedBlockSize(*config, pindexPrev);
    //8. 返回当前块的截止时间
    nLockTimeCutoff =
        (STANDARD_LOCKTIME_VERIFY_FLAGS & LOCKTIME_MEDIAN_TIME_PAST)
            ? pindexPrev->GetMedianTimePast()
            : pblock->GetBlockTime();

    //9 从交易池选择高优先级的交易，打包到块中，只允许占块容量的5%(具体多少，的看一下)
    addPriorityTxs();
    int nPackagesSelected = 0;
    int nDescendantsUpdated = 0;
    //10. 从交易池选择交易，添加到块中，此时会填充到块的阈值大小，或交易池的交易都被打包
    addPackageTxs(nPackagesSelected, nDescendantsUpdated);

    //11. 获取Unix时间。
    int64_t nTime1 = GetTimeMicros();

    //12. 获取块打包完成后的交易数量和块大小
    nLastBlockTx = nBlockTx;
    nLastBlockSize = nBlockSize;

    //13.创建coinbase交易
    // Create coinbase transaction.
    CMutableTransaction coinbaseTx;
    coinbaseTx.vin.resize(1);
    coinbaseTx.vin[0].prevout.SetNull();
    coinbaseTx.vout.resize(1);
    coinbaseTx.vout[0].scriptPubKey = scriptPubKeyIn;
    coinbaseTx.vout[0].nValue =
        nFees + GetBlockSubsidy(nHeight, chainparams.GetConsensus());       //计算coinbase的输出金额
    coinbaseTx.vin[0].scriptSig = CScript() << nHeight << OP_0;             //写coinbase的输入脚本
    pblock->vtx[0] = MakeTransactionRef(coinbaseTx);                        //交易集合的0号位置填充为coinbase交易
    pblocktemplate->vTxFees[0] = -1 * nFees;                                //

    //14. 获取块的序列化大小
    uint64_t nSerializeSize =
        GetSerializeSize(*pblock, SER_NETWORK, PROTOCOL_VERSION);

    LogPrintf("CreateNewBlock(): total size: %u txs: %u fees: %ld sigops %d\n",
              nSerializeSize, nBlockTx, nFees, nBlockSigOps);

    // Fill in header.
    //15. 给块头赋值
    pblock->hashPrevBlock = pindexPrev->GetBlockHash();
    UpdateTime(pblock, chainparams.GetConsensus(), pindexPrev);
    pblock->nBits =
        GetNextWorkRequired(pindexPrev, pblock, chainparams.GetConsensus());
    pblock->nNonce = 0;
    pblocktemplate->vTxSigOpsCount[0] =
        GetSigOpCountWithoutP2SH(*pblock->vtx[0]);

    CValidationState state;

    if (!TestBlockValidity(*config, state, chainparams, *pblock, pindexPrev,
                           false, false)) {
        throw std::runtime_error(strprintf("%s: TestBlockValidity failed: %s",
                                           __func__,
                                           FormatStateMessage(state)));
    }
    int64_t nTime2 = GetTimeMicros();

    LogPrint("bench", "CreateNewBlock() packages: %.2fms (%d packages, %d "
                      "updated descendants), validity: %.2fms (total %.2fms)\n",
             0.001 * (nTime1 - nTimeStart), nPackagesSelected,
             nDescendantsUpdated, 0.001 * (nTime2 - nTime1),
             0.001 * (nTime2 - nTimeStart));

    return std::move(pblocktemplate);
}

//查看一个交易的所有父交易是否都已经被添加到块中； 没有被全部添加，返回true。 否则，返回false.
bool BlockAssembler::isStillDependent(CTxMemPool::txiter iter) {
    for (CTxMemPool::txiter parent : mempool.GetMemPoolParents(iter)) {
        if (!inBlock.count(parent)) {
            return true;
        }
    }
    return false;
}

//遍历集合中的交易，删除已被打包的交易。
void BlockAssembler::onlyUnconfirmed(CTxMemPool::setEntries &testSet) {
    // 遍历
    for (CTxMemPool::setEntries::iterator iit = testSet.begin();
         iit != testSet.end();) {
        // 删除已经被打包的交易。
        // Only test txs not already in the block.
        if (inBlock.count(*iit)) {
            testSet.erase(iit++);
        } else {
            iit++;
        }
    }
}

//测试一个这个交易添加到块中 是否适合。检测 块的大小和操作码。
//合格，返回true, 否则，返回false。
bool BlockAssembler::TestPackage(uint64_t packageSize, int64_t packageSigOps) {
    //1. 如果打包该交易后，大于当前块的最大容量，返回false。
    auto blockSizeWithPackage = nBlockSize + packageSize;
    if (blockSizeWithPackage >= nMaxGeneratedBlockSize) {
        return false;
    }
    //2. 如果打包该交易后，操作码大于标准字节限制下的操作码数量，返回false。
    if (nBlockSigOps + packageSigOps >=
        GetMaxBlockSigOpsCount(blockSizeWithPackage)) {
        return false;
    }
    return true;
}

// Perform transaction-level checks before adding to block:
// - transaction finality (locktime)
// - serialized size (in case -blockmaxsize is in use)
// 在添加到块以前，执行交易等级检查。(交易的成熟度，序列化字节。)
bool BlockAssembler::TestPackageTransactions(
    const CTxMemPool::setEntries &package) {
    //1. 缓冲当前的块大小
    uint64_t nPotentialBlockSize = nBlockSize;
    //2. 遍历整个交易集合
    for (const CTxMemPool::txiter it : package) {
        CValidationState state;
        //3. 检查交易是否可以打包，不可以，退出。
        if (!ContextualCheckTransaction(*config, it->GetTx(), state,
                                        chainparams.GetConsensus(), nHeight,
                                        nLockTimeCutoff)) {
            return false;
        }
        //4. 获取交易的字节大小。
        uint64_t nTxSize =
            ::GetSerializeSize(it->GetTx(), SER_NETWORK, PROTOCOL_VERSION);
        //5. 如果该交易的字节大小 + 当前要添加的交易大于块的限制大小，退出。
        if (nPotentialBlockSize + nTxSize >= nMaxGeneratedBlockSize) {
            return false;
        }
        //6. 当前块的大小+当前要添加交易的大小
        nPotentialBlockSize += nTxSize;
    }
    //7. 如果交易检查通过(成熟且带重放保护)，并且整个交易集合添加到 块上后，仍然符合块大小。返回true.
    return true;
}

// 测试一个交易是否适合 添加到块中。(该方法用于添加优先级交易，查看优先级是否足够，以及是否有足够的空间)
bool BlockAssembler::TestForBlock(CTxMemPool::txiter it) {
    //1. 计算添加该交易后的 块大小
    auto blockSizeWithTx =
        nBlockSize +
        ::GetSerializeSize(it->GetTx(), SER_NETWORK, PROTOCOL_VERSION);
    //2. 将该大小与块的最大字节 比较。
    if (blockSizeWithTx >= nMaxGeneratedBlockSize) {
        // 如果块此时真正的大小 大于 最大值的-100， 或者最后添加交易时尝试的次数大于50，
        // 标识该区块已填充完成，返回false,该交易不适合在向区块中添加。
        if (nBlockSize > nMaxGeneratedBlockSize - 100 || lastFewTxs > 50) {
            blockFinished = true;
            return false;
        }
        // 标识当前块的字节数 > 最大值-1000(为coinbase交易预留的空间)；更新尝试的次数。
        if (nBlockSize > nMaxGeneratedBlockSize - 1000) {
            lastFewTxs++;
        }
        return false;
    }

    //3. 获取该字节下的标准的最大签名操纵码个数。
    auto maxBlockSigOps = GetMaxBlockSigOpsCount(blockSizeWithTx);
    //4. 判断当前的块操作码数量+该交易的操作码数量是否符合 共识规则。如果不符合，进入下列规则
    if (nBlockSigOps + it->GetSigOpCount() >= maxBlockSigOps) {
        // If the block has room for no more sig ops then flag that the block is
        // finished. 如果该块的签名操作码数量 在该字节下达到极限，则标识该块已经打包完成。
        // TODO: We should consider adding another transaction that isn't very
        // dense in sigops instead of bailing out so easily.
        // 改进，此处应该是尝试添加另一个操作码不是特别多的交易，而不是直接退出。
        if (nBlockSigOps > maxBlockSigOps - 2) {
            blockFinished = true;
            return false;
        }
        // Otherwise attempt to find another tx with fewer sigops to put in the
        // block. 否则，去查找另一个操作码不是特别稠密的交易，将它放到块中。
        return false;
    }

    // Must check that lock times are still valid. This can be removed once MTP
    // is always enforced as long as reorgs keep the mempool consistent.
    //5. 检查该交易针对于该区块的状态，是否该交易已成熟。不成熟，返回false。
    CValidationState state;
    if (!ContextualCheckTransaction(*config, it->GetTx(), state,
                                    chainparams.GetConsensus(), nHeight,
                                    nLockTimeCutoff)) {
        return false;
    }

    return true;
}

//将交易添加到块中。
void BlockAssembler::AddToBlock(CTxMemPool::txiter iter) {
    //1. 向块中加入该交易，并将该交易的交易费，签名操作数加入状态中。
    pblock->vtx.emplace_back(iter->GetSharedTx());
    pblocktemplate->vTxFees.push_back(iter->GetFee());
    pblocktemplate->vTxSigOpsCount.push_back(iter->GetSigOpCount());
    nBlockSize += iter->GetTxSize();        //累计当前的块大小
    ++nBlockTx;                             //累计当前的交易数量
    nBlockSigOps += iter->GetSigOpCount();  //累计当前的块中所有操作码的数量
    nFees += iter->GetFee();                //累计块中的交易费
    inBlock.insert(iter);                   //将交易池中的条目加入状态中

    //2. 是否打印交易的优先级，默认不打印
    bool fPrintPriority = GetBoolArg("-printpriority", DEFAULT_PRINTPRIORITY);
    //如果打印，则获取交易的优先级。
    if (fPrintPriority) {
        double dPriority = iter->GetPriority(nHeight);
        Amount dummy;
        mempool.ApplyDeltas(iter->GetTx().GetId(), dPriority, dummy);
        LogPrintf(
            "priority %.1f fee %s txid %s\n", dPriority,
            CFeeRate(iter->GetModifiedFee(), iter->GetTxSize()).ToString(),
            iter->GetTx().GetId().ToString());
    }
}

// 遍历已被添加到块中的交易(alreadyAdded)， 查找它们所有在交易池中的后代交易，然后将这些后代交易添加到
// 临时集合中(mapModifiedTx); 并返回更新这些后代交易状态的次数。
int BlockAssembler::UpdatePackagesForAdded(
    const CTxMemPool::setEntries &alreadyAdded,
    indexed_modified_transaction_set &mapModifiedTx) {
    int nDescendantsUpdated = 0;

    // 1. 遍历所有已经添加到块中的交易。
    for (const CTxMemPool::txiter it : alreadyAdded) {
        CTxMemPool::setEntries descendants;
        //2. 获取该交易在交易池中的所有后代交易。
        mempool.CalculateDescendants(it, descendants);
        //3. 遍历它所有的后代交易
        // Insert all descendants (not yet in block) into the modified set.
        for (CTxMemPool::txiter desc : descendants) {
            //4. 如果该后代交易已经被添加到块中，跳过，继续下次循环
            if (alreadyAdded.count(desc)) {
                continue;
            }
            ++nDescendantsUpdated;

            //5. 该后代交易未被添加，判断该交易是否存在于 mapModifiedTx 中(因为一个交易可能是多个交易的后代)。
            modtxiter mit = mapModifiedTx.find(desc);
            //6. 不存在，构造一个可以修改的交易条目，修改条目的祖先状态(减去已被添加的交易)，并将该交易插入mapModifiedTx中，
            if (mit == mapModifiedTx.end()) {
                //构建一个新的对象
                CTxMemPoolModifiedEntry modEntry(desc);
                modEntry.nSizeWithAncestors -= it->GetTxSize();
                modEntry.nModFeesWithAncestors -= it->GetModifiedFee();
                modEntry.nSigOpCountWithAncestors -= it->GetSigOpCount();
                mapModifiedTx.insert(modEntry);
            } else {
                // 如果存在，不需重复添加，只要减少该交易的祖先状态即可(因为它的祖先已经被添加到块中)
                mapModifiedTx.modify(mit, update_for_parent_inclusion(it));
            }
        }
    }

    // 返回已被添加到块中交易的 后代条目更新状态的次数。
    return nDescendantsUpdated;
}

// Skip entries in mapTx that are already in a block or are present in
// mapModifiedTx (which implies that the mapTx ancestor state is stale due to
// ancestor inclusion in the block). Also skip transactions that we've already
// failed to add. This can happen if we consider a transaction in mapModifiedTx
// and it fails: we can then potentially consider it again while walking mapTx.
// It's currently guaranteed to fail again, but as a belt-and-suspenders check
// we put it in failedTx and avoid re-evaluation, since the re-evaluation would
// be using cached size/sigops/fee values that are not actually correct.
// 跳过条目
bool BlockAssembler::SkipMapTxEntry(
    CTxMemPool::txiter it, indexed_modified_transaction_set &mapModifiedTx,
    CTxMemPool::setEntries &failedTx) {
    //1. 该交易存在于 交易池
    assert(it != mempool.mapTx.end());
    //2. 它存在于 临时集合中，或已被打包到块中，或存在于失败集合中， 返回true,标识跳过给条目。
    if (mapModifiedTx.count(it) || inBlock.count(it) || failedTx.count(it)) {
        return true;
    }
    return false;
}

//排序集合中的交易。sortedEntries(out):排序后的集合。package(in):要排序的集合，祖先交易
//entry(in):依据该交易产生的祖先交易。该条目未被使用，因为该条目已经被插入package中。
void BlockAssembler::SortForBlock(
    const CTxMemPool::setEntries &package, CTxMemPool::txiter entry,
    std::vector<CTxMemPool::txiter> &sortedEntries) {
    // Sort package by ancestor count. If a transaction A depends on transaction
    // B, then A's ancestor count must be greater than B's. So this is
    // sufficient to validly order the transactions for block inclusion.
    sortedEntries.clear();
    sortedEntries.insert(sortedEntries.begin(), package.begin(), package.end());
    std::sort(sortedEntries.begin(), sortedEntries.end(),
              CompareTxIterByAncestorCount());
}

// This transaction selection algorithm orders the mempool based on feerate of a
// transaction including all unconfirmed ancestors. Since we don't remove
// transactions from the mempool as we select them for block inclusion, we need
// an alternate method of updating the feerate of a transaction with its
// not-yet-selected ancestors as we go. This is accomplished by walking the
// in-mempool descendants of selected transactions and storing a temporary
// modified state in mapModifiedTxs. Each time through the loop, we compare the
// best transaction in mapModifiedTxs with the next transaction in the mempool
// to decide what transaction package to work on next.
// 这个交易选择算法根据 包含所有未确认的祖先交易平均费率来订购mempool. 我们不会从交易池删除交易，
// 因为需要选择这些交易来填充区块，因此我们需要一种替代方法来更新尚未选定的祖先交易的费率。
// 每次通过循环，我们都会比较 mapModifiedTxs 中的最佳交易与mempool中下一个交易进行比较，来决定去打包那个交易。
//nPackagesSelected(out):这轮被被打包交易的次数。
//nDescendantsUpdated(out): 返回这些被添加交易后代的更新次数。
void BlockAssembler::addPackageTxs(int &nPackagesSelected,
                                   int &nDescendantsUpdated) {
    // mapModifiedTx will store sorted packages after they are modified because
    // some of their txs are already in the block.
    indexed_modified_transaction_set mapModifiedTx;
    // Keep track of entries that failed inclusion, to avoid duplicate work.
    CTxMemPool::setEntries failedTx;

    // Start by adding all descendants of previously added txs to mapModifiedTx
    // and modifying them for their already included ancestors.
    //1. 将已经添加到块的交易的 所有后代交易添加到   mapModifiedTx 中，并修改他们的祖先交易状态。
    // mapModifiedTx 中存储的都是在交易池中的交易。
    UpdatePackagesForAdded(inBlock, mapModifiedTx);

    //2. 获取交易池中以 祖先积分进行排序的交易。
    CTxMemPool::indexed_transaction_set::index<ancestor_score>::type::iterator
        mi = mempool.mapTx.get<ancestor_score>().begin();
    CTxMemPool::txiter iter;

    // Limit the number of attempts to add transactions to the block when it is
    // close to full; this is just a simple heuristic to finish quickly if the
    // mempool has a lot of entries.
    // 限制在块接近完成时，向块中添加交易的次数。
    const int64_t MAX_CONSECUTIVE_FAILURES = 1000;
    int64_t nConsecutiveFailed = 0;

    //3. 遍历整个交易池(以祖先积分为顺序)，以及刚才的存储数据的临时变量
    while (mi != mempool.mapTx.get<ancestor_score>().end() ||
           !mapModifiedTx.empty()) {
        // First try to find a new transaction in mapTx to evaluate.
        //3. 遍历当前交易池的首个交易， 判断是否已在块中，已在临时存储集合中，是否已在失败集合中。
        // 存在，则跳过该交易，继续接下来的循环
        if (mi != mempool.mapTx.get<ancestor_score>().end() &&
            SkipMapTxEntry(mempool.mapTx.project<0>(mi), mapModifiedTx,
                           failedTx)) {
            ++mi;
            continue;
        }

        // 4.到这步的交易就不是陈旧的，判断要将那个交易 进行评估。
        // Now that mi is not stale, determine which transaction to evaluate:
        // the next entry from mapTx, or the best from mapModifiedTx?
        bool fUsingModified = false;

        modtxscoreiter modit = mapModifiedTx.get<ancestor_score>().begin();
        //5. 标识这个 交易来自临时集合(可能这个条目已从 交易池中删除)
        if (mi == mempool.mapTx.get<ancestor_score>().end()) {
            // We're out of entries in mapTx; use the entry from mapModifiedTx
            iter = modit->iter;
            fUsingModified = true;
        } else {
            // Try to compare the mapTx entry to the mapModifiedTx entry.
            //6. 从交易池中取该交易 以哈希进行排序的迭代器。 这个条目所指的交易会被存入块中
            iter = mempool.mapTx.project<0>(mi);
            //7. 如果临时集合中还存在数据，则将临时集合中的数据 与交易池中 的数据进行比较
            if (modit != mapModifiedTx.get<ancestor_score>().end() &&
                CompareModifiedEntry()(*modit, CTxMemPoolModifiedEntry(iter))) {
                // The best entry in mapModifiedTx has higher score than the one
                // from mapTx. Switch which transaction (package) to consider
                iter = modit->iter;
                fUsingModified = true;
            } else {
                // 临时集合中不存在该条目，或它是
                // Either no entry in mapModifiedTx, or it's worse than mapTx.
                // Increment mi for the next loop iteration.
                ++mi;
            }
        }

        // We skip mapTx entries that are inBlock, and mapModifiedTx shouldn't
        // contain anything that is inBlock.
        // 此时这个条目一定不包含在 块中，并且临时集合中的元素都不包含在块中
        assert(!inBlock.count(iter));

        uint64_t packageSize = iter->GetSizeWithAncestors();
        Amount packageFees = iter->GetModFeesWithAncestors();
        int64_t packageSigOps = iter->GetSigOpCountWithAncestors();
        //8. 使用临时集合中的交易
        if (fUsingModified) {
            packageSize = modit->nSizeWithAncestors;
            packageFees = modit->nModFeesWithAncestors;
            packageSigOps = modit->nSigOpCountWithAncestors;
        }

        //9. 获取该交易字节数 在当前块费率下需要的交易费； 交易费太低的，跳过。
        // 最低费率； packageSize  = packageFees
        if (packageFees < blockMinFeeRate.GetFee(packageSize)) {
            // Everything else we might consider has a lower fee rate
            // 我们可能认为有一个最低的交易费率。
            return;
        }

        //10. 测试这个交易添加到当前块中是否合适。不合适，进入下列条件。
        if (!TestPackage(packageSize, packageSigOps)) {
            // 如果使用的是临时集合中的交易，
            if (fUsingModified) {
                // Since we always look at the best entry in mapModifiedTx, we
                // must erase failed entries so that we can consider the next
                // best entry on the next loop iteration
                // 从临时集合中删除它，并将这个条目加入失败集合中。
                mapModifiedTx.get<ancestor_score>().erase(modit);
                failedTx.insert(iter);
            }
            // 更新连续失败的次数。
            ++nConsecutiveFailed;
            // 如果失败的次数大于共识，且块已经达到标准限值，此时，退出添加操作，函数返回。
            if (nConsecutiveFailed > MAX_CONSECUTIVE_FAILURES &&
                nBlockSize > nMaxGeneratedBlockSize - 1000) {
                // Give up if we're close to full and haven't succeeded in a
                // while.
                break;
            }
            // 没有达到条件，继续下次循环。
            continue;
        }

        CTxMemPool::setEntries ancestors;
        uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
        std::string dummy;
        //11. 计算该交易的祖先交易。
        mempool.CalculateMemPoolAncestors(*iter, ancestors, nNoLimit, nNoLimit,
                                          nNoLimit, nNoLimit, dummy, false);
        //12. 遍历祖先的集合交易，删除已被打包的祖先交易。
        onlyUnconfirmed(ancestors);
        //13. 将这个交易加入 祖先集合。
        ancestors.insert(iter);

        // Test if all tx's are Final
        // 14. 检查整个 交易集合添加到块中，是否满足块的大小，以及这些添加的交易是否成熟。
        // 不符合条件，进入下列操作
        if (!TestPackageTransactions(ancestors)) {
            // 如果使用了临时集合中的交易，
            if (fUsingModified) {
                // 从临时集合中删除它，并将这个删除的交易加入 失败集合中。继续下次循环
                mapModifiedTx.get<ancestor_score>().erase(modit);
                failedTx.insert(iter);
            }
            continue;
        }

        // This transaction will make it in; reset the failed counter.
        //15. 重置连续失败的次数，因为这次想块中添加交易成功。
        nConsecutiveFailed = 0;

        // Package can be added. Sort the entries in a valid order.
        //16. 这个 ancestors 集合中的交易可以重新排序后被添加进块，
        std::vector<CTxMemPool::txiter> sortedEntries;
        SortForBlock(ancestors, iter, sortedEntries);

        //17. 遍历排序后的集合，将这些交易加入块中。并从临时集合中删除这些交易。
        for (size_t i = 0; i < sortedEntries.size(); ++i) {
            //添加交易到块中，并更新块的状态
            AddToBlock(sortedEntries[i]);
            // Erase from the modified set, if present； 从临时集合中删除该交易
            mapModifiedTx.erase(sortedEntries[i]);
        }

        //18. 累计打包交易的数量
        ++nPackagesSelected;

        // Update transactions that depend on each of these
        //19. 累计这些添加的交易后代被更新的次数。
        nDescendantsUpdated += UpdatePackagesForAdded(ancestors, mapModifiedTx);
    }
}

//向块中添加优先级交易
void BlockAssembler::addPriorityTxs() {
    // How much of the block should be dedicated to high-priority transactions,
    // included regardless of the fees they pay.
    //1. 默认预留 块空间 5%的容量 来添加高优先级的交易
    if (config->GetBlockPriorityPercentage() == 0) {
        return;
    }

    //2. 获取优先级交易可以使用的块大小。
    uint64_t nBlockPrioritySize =
        nMaxGeneratedBlockSize * config->GetBlockPriorityPercentage() / 100;

    // This vector will be sorted into a priority queue:
    //3. 排序优先交易的序列
    std::vector<TxCoinAgePriority> vecPriority;
    TxCoinAgePriorityCompare pricomparer;
    // 此处存放交易和它的优先级
    std::map<CTxMemPool::txiter, double, CTxMemPool::CompareIteratorByHash>
        waitPriMap;
    typedef std::map<CTxMemPool::txiter, double,
                     CTxMemPool::CompareIteratorByHash>::iterator waitPriIter;
    double actualPriority = -1;

    //4. 获取交易池中所有交易以及 它们的优先级
    vecPriority.reserve(mempool.mapTx.size());
    for (CTxMemPool::indexed_transaction_set::iterator mi =
             mempool.mapTx.begin();
         mi != mempool.mapTx.end(); ++mi) {
        double dPriority = mi->GetPriority(nHeight);
        Amount dummy;
        mempool.ApplyDeltas(mi->GetTx().GetId(), dPriority, dummy);
        vecPriority.push_back(TxCoinAgePriority(dPriority, mi));
    }
    // 对集合中的所有元素做堆排序
    std::make_heap(vecPriority.begin(), vecPriority.end(), pricomparer);

    CTxMemPool::txiter iter;

    // Add a tx from priority queue to fill the part of block reserved to
    // priority transactions.
    //5. 从优先级交易集合中选出一个交易填充到 块中。
    while (!vecPriority.empty() && !blockFinished) {
        //6. 取出排序的最大值元素，并从集合中删除它
        iter = vecPriority.front().second;
        actualPriority = vecPriority.front().first;
        std::pop_heap(vecPriority.begin(), vecPriority.end(), pricomparer);
        vecPriority.pop_back();

        // If tx already in block, skip.
        //7. 如果这个优先级交易已被添加，就断言出错。
        if (inBlock.count(iter)) {
            // Shouldn't happen for priority txs.
            assert(false);
            continue;
        }

        // If tx is dependent on other mempool txs which haven't yet been
        // included then put it in the waitSet.
        //8. 如果这个添加的交易 依赖交易池中其他还没有被添加的交易，将它添加到等待集合中。
        // 继续下次循环
        if (isStillDependent(iter)) {
            waitPriMap.insert(std::make_pair(iter, actualPriority));
            continue;
        }

        // If this tx fits in the block add it, otherwise keep looping.
        //9. 如果这个交易适合添加到块中，就进入下列逻辑
        if (TestForBlock(iter)) {
            //10. 将该交易添加到区块中。
            AddToBlock(iter);

            // If now that this txs is added we've surpassed our desired
            // priority size or have dropped below the AllowFreeThreshold, then
            // we're done adding priority txs.
            //11. 如果当前的块大小已经超过了阈值，或者已经降到了允许添加免费交易的阈值下，则添加优先级完成，退出该方法。
            if (nBlockSize >= nBlockPrioritySize ||
                !AllowFree(actualPriority)) {
                break;
            }

            // This tx was successfully added, so add transactions that depend
            // on this one to the priority queue to try again.
            //12. 获取该交易的子交易集合，遍历它的所有子交易，查看待等待队列中是否含有这些子交易，
            // 如果有，就将这些子交易添加到 优先级队列中，并从等待队列中删除这些子交易。
            for (CTxMemPool::txiter child : mempool.GetMemPoolChildren(iter)) {
                waitPriIter wpiter = waitPriMap.find(child);
                if (wpiter != waitPriMap.end()) {
                    vecPriority.push_back(
                        TxCoinAgePriority(wpiter->second, child));
                    std::push_heap(vecPriority.begin(), vecPriority.end(),
                                   pricomparer);
                    waitPriMap.erase(wpiter);
                }
            }
        }
    }
}

void IncrementExtraNonce(const Config &config, CBlock *pblock,
                         const CBlockIndex *pindexPrev,
                         unsigned int &nExtraNonce) {
    // Update nExtraNonce
    static uint256 hashPrevBlock;
    if (hashPrevBlock != pblock->hashPrevBlock) {
        nExtraNonce = 0;
        hashPrevBlock = pblock->hashPrevBlock;
    }
    ++nExtraNonce;
    // Height first in coinbase required for block.version=2
    unsigned int nHeight = pindexPrev->nHeight + 1;
    CMutableTransaction txCoinbase(*pblock->vtx[0]);
    txCoinbase.vin[0].scriptSig =
        (CScript() << nHeight << CScriptNum(nExtraNonce)
                   << getExcessiveBlockSizeSig(config)) +
        COINBASE_FLAGS;
    assert(txCoinbase.vin[0].scriptSig.size() <= MAX_COINBASE_SCRIPTSIG_SIZE);

    pblock->vtx[0] = MakeTransactionRef(std::move(txCoinbase));
    pblock->hashMerkleRoot = BlockMerkleRoot(*pblock);
}
