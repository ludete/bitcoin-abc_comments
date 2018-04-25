// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "txmempool.h"

#include "chainparams.h" // for GetConsensus.
#include "clientversion.h"
#include "config.h"
#include "consensus/consensus.h"
#include "consensus/validation.h"
#include "policy/fees.h"
#include "policy/policy.h"
#include "streams.h"
#include "timedata.h"
#include "util.h"
#include "utilmoneystr.h"
#include "utiltime.h"
#include "validation.h"
#include "version.h"

#include <boost/range/adaptor/reversed.hpp>

// tx(in):进入交易池的交易；fnee(in):该交易的交易费。nTime(in):交易进入交易池的时间。
// entryPriority(in): ; entryHeight(in): 该交易进入交易池时，主链的高度。
// inChainInputValue(in): 该交易的输入金额。spendsCoinbase(in):是否花费coinbase交易。
// sigOpsCount(in):该交易的签名操作个数。lp(in):该交易的锁定点，交易只有达到这个点之后，才会被打包。
CTxMemPoolEntry::CTxMemPoolEntry(const CTransactionRef &_tx, const Amount _nFee,
                                 int64_t _nTime, double _entryPriority,
                                 unsigned int _entryHeight,
                                 Amount _inChainInputValue,
                                 bool _spendsCoinbase, int64_t _sigOpsCount,
                                 LockPoints lp)
    : tx(_tx), nFee(_nFee), nTime(_nTime), entryPriority(_entryPriority),
      entryHeight(_entryHeight), inChainInputValue(_inChainInputValue),
      spendsCoinbase(_spendsCoinbase), sigOpCount(_sigOpsCount),
      lockPoints(lp) {
    nTxSize = GetTransactionSize(*tx);
    nModSize = tx->CalculateModifiedSize(GetTxSize());
    nUsageSize = RecursiveDynamicUsage(*tx) + memusage::DynamicUsage(tx);

    nCountWithDescendants = 1;
    nSizeWithDescendants = GetTxSize();
    nModFeesWithDescendants = nFee;
    Amount nValueIn = tx->GetValueOut() + nFee;
    assert(inChainInputValue <= nValueIn);

    feeDelta = 0;

    nCountWithAncestors = 1;
    nSizeWithAncestors = GetTxSize();
    nModFeesWithAncestors = nFee;
    nSigOpCountWithAncestors = sigOpCount;
}

CTxMemPoolEntry::CTxMemPoolEntry(const CTxMemPoolEntry &other) {
    *this = other;
}

// currentHeight(in):交易进入交易池时，主链的下个区块的高度(Tip +1)
//获取交易池中交易条目基于某个高度时的优先级
double CTxMemPoolEntry::GetPriority(unsigned int currentHeight) const {
    //高度差*交易的引用输入总金额 / 可修改的交易大小
    double deltaPriority = double((currentHeight - entryHeight) *
                                  inChainInputValue.GetSatoshis()) /
                           nModSize;
    //将两次的优先级进行累加
    double dResult = entryPriority + deltaPriority;
    // This should only happen if it was called with a height below entry height
    // dResult<0这种情况之只可能发生在一个调用高度 < 交易进入交易池时的高度(意味着块链重组时，主链的高度大幅度降低)
    if (dResult < 0) dResult = 0;
    return dResult;
}

void CTxMemPoolEntry::UpdateFeeDelta(Amount newFeeDelta) {
    nModFeesWithDescendants += newFeeDelta - feeDelta;
    nModFeesWithAncestors += newFeeDelta - feeDelta;
    feeDelta = newFeeDelta;
}

void CTxMemPoolEntry::UpdateLockPoints(const LockPoints &lp) {
    lockPoints = lp;
}

// Update the given tx for any in-mempool descendants.
// Assumes that setMemPoolChildren is correct for the given tx and all
// descendants.
//更新给定交易在交易池中的所有后代交易。假设setMemPoolChildren对于给定的tx和它所有的后代交易是正确的。
//cachedDescendants(out):传出集合； setExclude(in):在交易池中的交易集合
void CTxMemPool::UpdateForDescendants(txiter updateIt,
                                      cacheMap &cachedDescendants,
                                      const std::set<uint256> &setExclude) {
    setEntries stageEntries, setAllDescendants;     //值语义
    //1. 获取该交易的子交易集合
    stageEntries = GetMemPoolChildren(updateIt);

    //2. 遍历所有的子交易，获取该交易的所有后代交易。
    while (!stageEntries.empty()) {
        //3. 将子交易集合中的交易插入 后代交易集合中
        const txiter cit = *stageEntries.begin();
        setAllDescendants.insert(cit);
        stageEntries.erase(cit);        //删除临时集合中的元素

        //4. 获取该子交易的子交易集合
        const setEntries &setChildren = GetMemPoolChildren(cit);
        for (const txiter childEntry : setChildren) {
            //5. 查看这个子交易集合中的交易是否在参数中，在的话，进入下列集合中。
            // 语句中
            cacheMap::iterator cacheIt = cachedDescendants.find(childEntry);
            if (cacheIt != cachedDescendants.end()) {
                // We've already calculated this one, just add the entries for
                // this set but don't traverse again.
                for (const txiter cacheEntry : cacheIt->second) {
                    setAllDescendants.insert(cacheEntry);
                }
            } else if (!setAllDescendants.count(childEntry)) {
                // 如果后代集合中没有这个交易，就将它加入临时集合中，进入下次循环。
                // Schedule for later processing
                stageEntries.insert(childEntry);
            }
        }
    }

    // setAllDescendants now contains all in-mempool descendants of updateIt.
    // Update and add to cached descendant map
    int64_t modifySize = 0;
    Amount modifyFee = 0;
    int64_t modifyCount = 0;
    //6. 遍历该交易的所有后代交易
    for (txiter cit : setAllDescendants) {
        if (!setExclude.count(cit->GetTx().GetId())) {
            modifySize += cit->GetTxSize();
            modifyFee += cit->GetModifiedFee();
            modifyCount++;
            cachedDescendants[updateIt].insert(cit);
            //7. 更新每个后代交易 的祖先状态
            // Update ancestor state for each descendant
            mapTx.modify(cit,
                         update_ancestor_state(updateIt->GetTxSize(),
                                               updateIt->GetModifiedFee(), 1,
                                               updateIt->GetSigOpCount()));
        }
    }
    // 8. 更新该交易的后代状态。
    mapTx.modify(updateIt,
                 update_descendant_state(modifySize, modifyFee, modifyCount));
}

// vHashesToUpdate is the set of transaction hashes from a disconnected block
// which has been re-added to the mempool. For each entry, look for descendants
// that are outside hashesToUpdate, and add fee/size information for such
// descendants to the parent. For each such descendant, also update the ancestor
// state to include the parent.
// 更新这些再次进入mempool中的交易的状态
void CTxMemPool::UpdateTransactionsFromBlock(
    const std::vector<uint256> &vHashesToUpdate) {
    LOCK(cs);
    // For each entry in vHashesToUpdate, store the set of in-mempool, but not
    // in-vHashesToUpdate transactions, so that we don't have to recalculate
    // descendants when we come across a previously seen entry.
    cacheMap mapMemPoolDescendantsToUpdate;

    // Use a set for lookups into vHashesToUpdate (these entries are already
    // accounted for in the state of their ancestors)
    std::set<uint256> setAlreadyIncluded(vHashesToUpdate.begin(),
                                         vHashesToUpdate.end());

    // Iterate in reverse, so that whenever we are looking at at a transaction
    // we are sure that all in-mempool descendants have already been processed.
    // This maximizes the benefit of the descendant cache and guarantees that
    // setMemPoolChildren will be updated, an assumption made in
    // UpdateForDescendants.
    //1. 方向迭代，以便它在交易池中的每个后代都已经被处理。
    for (const uint256 &hash : boost::adaptors::reverse(vHashesToUpdate)) {
        // we cache the in-mempool children to avoid duplicate updates
        // 缓存交易池中关于该交易的孩子条目，避免重复更新。
        setEntries setChildren;
        // calculate children from mapNextTx
        //2. 查看该交易是否在交易池中； 此处应该是存在交易池中。
        txiter it = mapTx.find(hash);
        if (it == mapTx.end()) {
            continue;
        }
        //3. 获取所有 依赖该交易的孩子交易。
        auto iter = mapNextTx.lower_bound(COutPoint(hash, 0));
        // First calculate the children, and update setMemPoolChildren to
        // include them, and update their setMemPoolParents to include this tx.
        //
        for (; iter != mapNextTx.end() && iter->first->hash == hash; ++iter) {
            //4. 获取这个交易在交易池中的所有子交易。
            const uint256 &childHash = iter->second->GetId();
            txiter childIter = mapTx.find(childHash);
            assert(childIter != mapTx.end());
            // We can skip updating entries we've encountered before or that are
            // in the block (which are already accounted for).
            //5. 缓存该交易的所有子交易，并且当这个子交易不在传入的交易集合中时，进入下列条件。
            //  更新这个交易的孩子交易集合； 更新孩子交易的父交易集合
            if (setChildren.insert(childIter).second &&
                !setAlreadyIncluded.count(childHash)) {
                //6. 更新该交易的子交易集合
                UpdateChild(it, childIter, true);
                //7. 更新该子交易的父交易集合
                UpdateParent(childIter, it, true);
            }
        }
        //8. 更新这个交易的所有后代交易状态。
        UpdateForDescendants(it, mapMemPoolDescendantsToUpdate,
                             setAlreadyIncluded);
    }
}

// entry(in):查询该交易在交易池中的所有祖先； 。
bool CTxMemPool::CalculateMemPoolAncestors(
    const CTxMemPoolEntry &entry, setEntries &setAncestors,
    uint64_t limitAncestorCount, uint64_t limitAncestorSize,
    uint64_t limitDescendantCount, uint64_t limitDescendantSize,
    std::string &errString, bool fSearchForParents /* = true */) const {
    LOCK(cs);

    setEntries parentHashes;
    const CTransaction &tx = entry.GetTx();

    //默认情况下进入这里；该参数的默认值为true, 查找该交易在交易池中的父交易。
    if (fSearchForParents) {
        // Get parents of this transaction that are in the mempool
        // GetMemPoolParents() is only valid for entries in the mempool, so we
        // iterate mapTx to find parents.
        // 查询该交易在交易池的父交易； 即它所引用输出的交易是否在交易池中；如果在，将它们添加到临时集合中
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            txiter piter = mapTx.find(tx.vin[i].prevout.hash);
            if (piter != mapTx.end()) {
                parentHashes.insert(piter);
                if (parentHashes.size() + 1 > limitAncestorCount) {
                    errString =
                        strprintf("too many unconfirmed parents [limit: %u]",
                                  limitAncestorCount);
                    return false;
                }
            }
        }
    } else {
        // If we're not searching for parents, we require this to be an entry in
        // the mempool already.
        txiter it = mapTx.iterator_to(entry);
        parentHashes = GetMemPoolParents(it);
    }

    size_t totalSizeWithAncestors = entry.GetTxSize();

    // 如果父交易集合不为空；
    while (!parentHashes.empty()) {
        txiter stageit = *parentHashes.begin();

        setAncestors.insert(stageit);
        parentHashes.erase(stageit);
        totalSizeWithAncestors += stageit->GetTxSize();

        if (stageit->GetSizeWithDescendants() + entry.GetTxSize() >
            limitDescendantSize) {
            errString = strprintf(
                "exceeds descendant size limit for tx %s [limit: %u]",
                stageit->GetTx().GetId().ToString(), limitDescendantSize);
            return false;
        } else if (stageit->GetCountWithDescendants() + 1 >
                   limitDescendantCount) {
            errString = strprintf("too many descendants for tx %s [limit: %u]",
                                  stageit->GetTx().GetId().ToString(),
                                  limitDescendantCount);
            return false;
        } else if (totalSizeWithAncestors > limitAncestorSize) {
            errString = strprintf("exceeds ancestor size limit [limit: %u]",
                                  limitAncestorSize);
            return false;
        }

        const setEntries &setMemPoolParents = GetMemPoolParents(stageit);
        for (const txiter &phash : setMemPoolParents) {
            // If this is a new ancestor, add it.
            if (setAncestors.count(phash) == 0) {
                parentHashes.insert(phash);
            }
            if (parentHashes.size() + setAncestors.size() + 1 >
                limitAncestorCount) {
                errString =
                    strprintf("too many unconfirmed ancestors [limit: %u]",
                              limitAncestorCount);
                return false;
            }
        }
    }

    return true;
}

//更新该交易所有的祖先交易信息；
//it(in):更新的交易； setAncestors(in):该交易的所有祖先交易; add(in):true,添加新交易； false, 删除新交易
void CTxMemPool::UpdateAncestorsOf(bool add, txiter it,
                                   setEntries &setAncestors) {
    //1. 获取该交易的父交易
    setEntries parentIters = GetMemPoolParents(it);

    // add or remove this tx as a child of each parent
    // 从父交易中添加或删除这个子交易
    for (txiter piter : parentIters) {
        UpdateChild(piter, it, add);
    }

    // 更新所有的祖先交易的状态
    const int64_t updateCount = (add ? 1 : -1);
    const int64_t updateSize = updateCount * it->GetTxSize();
    const Amount updateFee = updateCount * it->GetModifiedFee();
    for (txiter ancestorIt : setAncestors) {
        mapTx.modify(ancestorIt, update_descendant_state(updateSize, updateFee,
                                                         updateCount));
    }
}

// 更新这个交易中所有的祖先交易状态；
void CTxMemPool::UpdateEntryForAncestors(txiter it,
                                         const setEntries &setAncestors) {
    int64_t updateCount = setAncestors.size();
    int64_t updateSize = 0;
    Amount updateFee = 0;
    int64_t updateSigOpsCount = 0;
    for (txiter ancestorIt : setAncestors) {
        updateSize += ancestorIt->GetTxSize();
        updateFee += ancestorIt->GetModifiedFee();
        updateSigOpsCount += ancestorIt->GetSigOpCount();
    }
    mapTx.modify(it, update_ancestor_state(updateSize, updateFee, updateCount,
                                           updateSigOpsCount));
}

// 更新删除交易的所有子交易的父交易集合，将这个交易从父交易集合中删除。
void CTxMemPool::UpdateChildrenForRemoval(txiter it) {
    // 获取移除交易的子交易集合
    const setEntries &setMemPoolChildren = GetMemPoolChildren(it);
    for (txiter updateIt : setMemPoolChildren) {
        UpdateParent(updateIt, it, false);
    }
}

// 因为移除操作，更新交易池的状态；
// entriesToRemove(in): 移除交易的集合；updateDescendants(in):true：更新移除交易的所有后代交易；
// false：仅更新移除交易的子交易，这种存在于 删除交易的所有后代交易也被删除了。
// 函数执行完后，将entriesToRemove 集合中每个交易的子交易集合 中的交易，从这些交易的父集合中删除这个交易。
void CTxMemPool::UpdateForRemoveFromMempool(const setEntries &entriesToRemove,
                                            bool updateDescendants) {
    // For each entry, walk back all ancestors and decrement size associated
    // with this transaction.
    const uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();

    //1. 更新所有删除交易的 后代交易的祖先交易状态(祖先的数量，交易费，交易字节数，操作码数)。
    //  updateDescendants : true, 标识删除这个交易，并不删除它的后代交易，所以需要更新它的后代交易的祖先状态
    // updateDescendants : false, 标识删除这个交易以及它所有的后代交易，所以不需要再更新了(因为所有的后代交易都会被干掉)
    if (updateDescendants) {
        // updateDescendants should be true whenever we're not recursively
        // removing a tx and all its descendants, eg when a transaction is
        // confirmed in a block. Here we only update statistics and not data in
        // mapLinks (which we need to preserve until we're finished with all
        // operations that need to traverse the mempool).
        //  updateDescendants 应当为true，只要当我们不递归移除这个交易和它所有的后代交易，例如：当一个交易在块中被确认，
        // 只需要移除交易即可，不需要移除它的后代交易。此时我们只更新统计数据，而不是在mapLinks中的数据
        // 更新这写移除交易 所有后代的祖先状态
        for (txiter removeIt : entriesToRemove) {
            setEntries setDescendants;
            // 获取一个交易的所有的后代交易
            CalculateDescendants(removeIt, setDescendants);
            setDescendants.erase(removeIt); // don't update state for self
            int64_t modifySize = -((int64_t)removeIt->GetTxSize());
            Amount modifyFee = -1 * removeIt->GetModifiedFee();
            int modifySigOps = -removeIt->GetSigOpCount();

            // 仅更新这些后代交易的祖先交易的状态；如：祖先交易的大小，交易费等。
            for (txiter dit : setDescendants) {
                mapTx.modify(dit, update_ancestor_state(modifySize, modifyFee,
                                                        -1, modifySigOps));
            }
        }
    }

    // 更新删除交易 所有的祖先交易关于后代交易的状态，并更新该交易的父交易的子交易集合，将这个交易从集合中删除。
    for (txiter removeIt : entriesToRemove) {
        setEntries setAncestors;
        const CTxMemPoolEntry &entry = *removeIt;
        std::string dummy;
        // Since this is a tx that is already in the mempool, we can call CMPA
        // with fSearchForParents = false.  If the mempool is in a consistent
        // state, then using true or false should both be correct, though false
        // should be a bit faster.
        // However, if we happen to be in the middle of processing a reorg, then
        // the mempool can be in an inconsistent state. In this case, the set of
        // ancestors reachable via mapLinks will be the same as the set of
        // ancestors whose packages include this transaction, because when we
        // add a new transaction to the mempool in addUnchecked(), we assume it
        // has no children, and in the case of a reorg where that assumption is
        // false, the in-mempool children aren't linked to the in-block tx's
        // until UpdateTransactionsFromBlock() is called. So if we're being
        // called during a reorg, ie before UpdateTransactionsFromBlock() has
        // been called, then mapLinks[] will differ from the set of mempool
        // parents we'd calculate by searching, and it's important that we use
        // the mapLinks[] notion of ancestor transactions as the set of things
        // to update for removal.
        // 获取删除交易在交易池中的 所有的祖先交易
        CalculateMemPoolAncestors(entry, setAncestors, nNoLimit, nNoLimit,
                                  nNoLimit, nNoLimit, dummy, false);
        // Note that UpdateAncestorsOf severs the child links that point to
        // removeIt in the entries for the parents of removeIt.
        // 更新移除交易的 所有祖先交易的后代交易的状态。
        UpdateAncestorsOf(false, removeIt, setAncestors);
    }

    // After updating all the ancestor sizes, we can now sever the link between
    // each transaction being removed and any mempool children (ie, update
    // setMemPoolParents for each direct child of a transaction being removed).
    // 更新所有删除交易的 子交易的父交易集合， 将这个删除交易从集合中删除。
    for (txiter removeIt : entriesToRemove) {
        UpdateChildrenForRemoval(removeIt);
    }
}

void CTxMemPoolEntry::UpdateDescendantState(int64_t modifySize,
                                            Amount modifyFee,
                                            int64_t modifyCount) {
    nSizeWithDescendants += modifySize;
    assert(int64_t(nSizeWithDescendants) > 0);
    nModFeesWithDescendants += modifyFee;
    nCountWithDescendants += modifyCount;
    assert(int64_t(nCountWithDescendants) > 0);
}

void CTxMemPoolEntry::UpdateAncestorState(int64_t modifySize, Amount modifyFee,
                                          int64_t modifyCount,
                                          int modifySigOps) {
    nSizeWithAncestors += modifySize;
    assert(int64_t(nSizeWithAncestors) > 0);
    nModFeesWithAncestors += modifyFee;
    nCountWithAncestors += modifyCount;
    assert(int64_t(nCountWithAncestors) > 0);
    nSigOpCountWithAncestors += modifySigOps;
    assert(int(nSigOpCountWithAncestors) >= 0);
}

CTxMemPool::CTxMemPool(const CFeeRate &_minReasonableRelayFee)
    : nTransactionsUpdated(0) {
    // lock free clear
    _clear();

    // Sanity checks off by default for performance, because otherwise accepting
    // transactions becomes O(N^2) where N is the number of transactions in the
    // pool
    nCheckFrequency = 0;

    minerPolicyEstimator = new CBlockPolicyEstimator(_minReasonableRelayFee);
}

CTxMemPool::~CTxMemPool() {
    delete minerPolicyEstimator;
}

bool CTxMemPool::isSpent(const COutPoint &outpoint) {
    LOCK(cs);
    return mapNextTx.count(outpoint);
}

unsigned int CTxMemPool::GetTransactionsUpdated() const {
    LOCK(cs);
    return nTransactionsUpdated;
}

void CTxMemPool::AddTransactionsUpdated(unsigned int n) {
    LOCK(cs);
    nTransactionsUpdated += n;
}

//validFeeEstimate(in): 有效的交易费预估。entry(in):交易池条目。hash(in):该交易池的;
//setAncestors(in):该添加交易在交易池中的所有祖先交易。
bool CTxMemPool::addUnchecked(const uint256 &hash, const CTxMemPoolEntry &entry,
                              setEntries &setAncestors, bool validFeeEstimate) {
    NotifyEntryAdded(entry.GetSharedTx());
    // Add to memory pool without checking anything.
    // Used by AcceptToMemoryPool(), which DOES do all the appropriate checks.
    LOCK(cs);
    //1.  将新交易加入交易池
    indexed_transaction_set::iterator newit = mapTx.insert(entry).first;
    //2. 为新交易创建父子交易对
    mapLinks.insert(make_pair(newit, TxLinks()));

    // 此处在新代码中可以省略； 此处用来进行挖矿方面的设定
    // Update transaction for any feeDelta created by PrioritiseTransaction
    // 更新由优先级交易 创建的任何
    // TODO: refactor so that the fee delta is calculated before inserting into
    // mapTx.
    // 优先级，交易的优先级。
    std::map<uint256, std::pair<double, Amount>>::const_iterator pos =
        mapDeltas.find(hash);
    if (pos != mapDeltas.end()) {
        const std::pair<double, Amount> &deltas = pos->second;
        if (deltas.second != 0) {
            mapTx.modify(newit, update_fee_delta(deltas.second));
        }
    }

    // Update cachedInnerUsage to include contained transaction's usage.
    // (When we update the entry for in-mempool parents, memory usage will be
    // further updated.)
    //3. 更新交易池的消耗
    cachedInnerUsage += entry.DynamicMemoryUsage();

    //4. 构建交易池中的UTXO引用对；即每个交易的引用输入与该交易添加到交易池的缓存数据结构中。
    // 并将它的父交易哈希添加到临时父交易的集合中；Note：当一个交易的多个输入，引用了相同的一笔交易的不同输出，
    // 这个父交易只会被添加一次。
    const CTransaction &tx = newit->GetTx();
    std::set<uint256> setParentTransactions;
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        mapNextTx.insert(std::make_pair(&tx.vin[i].prevout, &tx));
        setParentTransactions.insert(tx.vin[i].prevout.hash);
    }
    // Don't bother worrying about child transactions of this one. Normal case
    // of a new transaction arriving is that there can't be any children,
    // because such children would be orphans. An exception to that is if a
    // transaction enters that used to be in a block. In that case, our
    // disconnect block logic will call UpdateTransactionsFromBlock to clean up
    // the mess we're leaving here.

    // Update ancestors with information about this tx；
    // 查询该交易的父交易是否在交易池中，并将这些在交易池的父交易添加到这个交易的父交易集合中，并更新交易池的内存使用量。
    for (const uint256 &phash : setParentTransactions) {
        txiter pit = mapTx.find(phash);
        if (pit != mapTx.end()) {
            UpdateParent(newit, pit, true);         //向该交易的父交易集合中 添加这些父交易
        }
    }
    // 更新祖先交易的后代状态。
    UpdateAncestorsOf(true, newit, setAncestors);
    // 更新添加交易的祖先状态
    UpdateEntryForAncestors(newit, setAncestors);

    nTransactionsUpdated++;
    totalTxSize += entry.GetTxSize();
    minerPolicyEstimator->processTransaction(entry, validFeeEstimate);

    vTxHashes.emplace_back(tx.GetHash(), newit);
    newit->vTxHashesIdx = vTxHashes.size() - 1;

    return true;
}

// 从交易池移除这个交易
void CTxMemPool::removeUnchecked(txiter it, MemPoolRemovalReason reason) {
    NotifyEntryRemoved(it->GetSharedTx(), reason);
    const uint256 txid = it->GetTx().GetId();
    for (const CTxIn &txin : it->GetTx().vin) {
        mapNextTx.erase(txin.prevout);
    }

    if (vTxHashes.size() > 1) {
        vTxHashes[it->vTxHashesIdx] = std::move(vTxHashes.back());
        vTxHashes[it->vTxHashesIdx].second->vTxHashesIdx = it->vTxHashesIdx;
        vTxHashes.pop_back();
        if (vTxHashes.size() * 2 < vTxHashes.capacity())
            vTxHashes.shrink_to_fit();
    } else
        vTxHashes.clear();

    totalTxSize -= it->GetTxSize();
    cachedInnerUsage -= it->DynamicMemoryUsage();
    cachedInnerUsage -= memusage::DynamicUsage(mapLinks[it].parents) +
                        memusage::DynamicUsage(mapLinks[it].children);
    mapLinks.erase(it);
    mapTx.erase(it);
    nTransactionsUpdated++;
    minerPolicyEstimator->removeTx(txid);
}

// Calculates descendants of entry that are not already in setDescendants, and
// adds to setDescendants. Assumes entryit is already a tx in the mempool and
// setMemPoolChildren is correct for tx and all descendants. Also assumes that
// if an entry is in setDescendants already, then all in-mempool descendants of
// it are already in setDescendants as well, so that we can save time by not
// iterating over those entries.
// 计算一个交易在交易池的所有后代交易
void CTxMemPool::CalculateDescendants(txiter entryit,
                                      setEntries &setDescendants) {
    //1. 临时交易集合，将所有不在 setDescendants 这个集合中的交易添加进这个变量中。
    setEntries stage;
    if (setDescendants.count(entryit) == 0) {
        stage.insert(entryit);
    }

    //2. 将临时集合中的所有交易都加入 后代交易集合中。此处可以递归查询到传入交易的所有后代交易，
    // 并将它们都放入后代交易的集合中。
    // Traverse down the children of entry, only adding children that are not
    // accounted for in setDescendants already (because those children have
    // either already been walked, or will be walked in this iteration).
    while (!stage.empty()) {
        txiter it = *stage.begin();
        setDescendants.insert(it);
        stage.erase(it);

        const setEntries &setChildren = GetMemPoolChildren(it);
        for (const txiter &childiter : setChildren) {
            if (!setDescendants.count(childiter)) {
                stage.insert(childiter);
            }
        }
    }
}

//递归删除产生冲突的交易； 应该删除该交易和它所有的后代交易
void CTxMemPool::removeRecursive(const CTransaction &origTx,
                                 MemPoolRemovalReason reason) {
    // Remove transaction from memory pool
    {
        LOCK(cs);
        setEntries txToRemove;
        txiter origit = mapTx.find(origTx.GetId());
        //1. 收集要删除的交易
        // 该交易在交易池中，进入下列条件
        if (origit != mapTx.end()) {
            txToRemove.insert(origit);
        } else {
            // 该交易不在交易池中，遍历交易池中，所有引用它作为输出的交易。
            // When recursively removing but origTx isn't in the mempool be sure
            // to remove any children that are in the pool. This can happen
            // during chain re-orgs if origTx isn't re-accepted into the mempool
            // for any reason.
            // 当递归删除的交易不在交易池中时，为了确保它的所有后代交易都被删除，我们需要查找交易池中是否有把它作为 UTXO来花费的交易。
            for (unsigned int i = 0; i < origTx.vout.size(); i++) {
                auto it = mapNextTx.find(COutPoint(origTx.GetId(), i));
                if (it == mapNextTx.end()) continue;
                txiter nextit = mapTx.find(it->second->GetId());
                assert(nextit != mapTx.end());
                txToRemove.insert(nextit);
            }
        }

        //2. 计算这些交易在交易池中的所有后代交易
        setEntries setAllRemoves;
        for (txiter it : txToRemove) {
            //计算该交易的所有后代交易
            CalculateDescendants(it, setAllRemoves);
        }

        //3. 移除 所有的交易
        RemoveStaged(setAllRemoves, false, reason);
    }
}

//重组链时，对交易池进行修改；此时会删除交易池中所有未成熟的交易，或引用输入已经被花费的交易。
//pcoins(in/out):UTXO集合。nMemPoolHeight(in):交易池高度，默认为当前主链的高度+1；flags(in):
void CTxMemPool::removeForReorg(const CCoinsViewCache *pcoins,
                                unsigned int nMemPoolHeight, int flags) {
    // 移除交易池中花费未成熟的UTXO的交易，因为块链进行了重组，可能以前成熟的块，现在变得未成熟。
    // Remove transactions spending a coinbase which are now immature and
    // no-longer-final transactions
    LOCK(cs);
    setEntries txToRemove;

    //1. 遍历交易池的所有交易，删除所有不成熟的交易。
    for (indexed_transaction_set::const_iterator it = mapTx.begin();
         it != mapTx.end(); it++) {

        //2. 获取交易的锁定点进行检测
        const CTransaction &tx = it->GetTx();
        LockPoints lp = it->GetLockPoints();
        //3. 测试交易池中的该交易是否还有效，(即该交易的引用输入是否还包含在主链中)
        bool validLP = TestLockPointValidity(&lp);

        auto &config = GetConfig();
        CValidationState state;

        //4. 非成熟交易，或没有采用重放攻击保护的交易，返回false。接着另一个检查，判断该交易输入的sequence字段是否可以被打包，否，返回false。
        if (!ContextualCheckTransactionForCurrentBlock(
                config, tx, state, config.GetChainParams().GetConsensus(),
                flags) ||
            !CheckSequenceLocks(tx, flags, &lp, validLP)) {

            // Note if CheckSequenceLocks fails the LockPoints may still be
            // invalid. So it's critical that we remove the tx and not depend on
            // the LockPoints.
            txToRemove.insert(it);
        } else if (it->GetSpendsCoinbase()) {
            //5. 如果一个交易通过了上面的检查，就继续检查该交易是否花费了一个coinbase交易

            // 遍历该交易的所有交易输入
            for (const CTxIn &txin : tx.vin) {

                //6. 查找这些引用输出的交易是否存在于交易池中， 如果存在，就略过该交易输入，因为coinbase交易不进入交易池。
                indexed_transaction_set::const_iterator it2 =
                    mapTx.find(txin.prevout.hash);
                if (it2 != mapTx.end()) {
                    continue;
                }

                //7. 在UTXO集合中查询该交易的这些引用输出所对应的UTXO。
                const Coin &coin = pcoins->AccessCoin(txin.prevout);

                //8. 标识开启mempool检查；则这些交易一定是未花费的。
                if (nCheckFrequency != 0) assert(!coin.IsSpent());

                //9. 如果有任何一个将花费的 UTXO已花费 或 将花费的coinbase还未成熟，也将这个交易加入待删除集合。
                if (coin.IsSpent() ||
                    (coin.IsCoinBase() &&
                     int64_t(nMemPoolHeight) - coin.GetHeight() <
                         COINBASE_MATURITY)) {
                    txToRemove.insert(it);
                    break;
                }
            }
        }

        //如果验证交易池交易自带的检测点，检测失败，更新该检测点。
        if (!validLP) {
            mapTx.modify(it, update_lock_points(lp));
        }
    }

    //10. 拿到删除集合后，删除这个集合中所有的交易和它的后代交易
    setEntries setAllRemoves;
    for (txiter it : txToRemove) {
        CalculateDescendants(it, setAllRemoves);
    }
    RemoveStaged(setAllRemoves, false, MemPoolRemovalReason::REORG);
}

// 移除冲突的交易，需要递归删除交易池中 所有与该交易 花费相同UTXO的交易；
// 因为该UTXO已被这个交易花费了，交易池中再花费这个UTXO的交易就违法了。
void CTxMemPool::removeConflicts(const CTransaction &tx) {
    // Remove transactions which depend on inputs of tx, recursively
    // 移除依赖该交易引用输入的交易，因为该交易已被打包进区块，这个UTXO已被花费，
    // 所以所有交易池中引用这些UTXO的也应该被删除
    LOCK(cs);
    for (const CTxIn &txin : tx.vin) {
        auto it = mapNextTx.find(txin.prevout);
        // 查找交易池中花费 与该交易的引用输出相同的交易；递归删除该交易和它的所有后代交易。
        if (it != mapNextTx.end()) {
            const CTransaction &txConflict = *it->second;
            if (txConflict != tx) {
                ClearPrioritisation(txConflict.GetId());
                // 这个交易 与删除的交易引用了相同的输出，这个删除的交易在此处为已经被确认的交易。
                // 所以需递归删除这个交易，以及它所有的子交易。
                removeRecursive(txConflict, MemPoolRemovalReason::CONFLICT);
            }
        }
    }
}

/**
 * Called when a block is connected. Removes from mempool and updates the miner
 * fee estimator.
 * vtx(in):要移除的块中的交易交易集合(因为该块中的交易已被打包)；
 * nBlockHeight(in):这些交易所对应的块高度
 * 从交易池中 移除块中包含的所有交易，并且更新矿工的挖矿费用。
 */
void CTxMemPool::removeForBlock(const std::vector<CTransactionRef> &vtx,
                                unsigned int nBlockHeight) {
    LOCK(cs);
    //1. 收集该区块中 在交易池中的交易
    std::vector<const CTxMemPoolEntry *> entries;
    for (const auto &tx : vtx) {
        uint256 txid = tx->GetId();

        indexed_transaction_set::iterator i = mapTx.find(txid);
        if (i != mapTx.end()) entries.push_back(&*i);
    }

    // Before the txs in the new block have been removed from the mempool,
    // update policy estimates
    //2. 在新块中的交易从mempool移除时，需要更新mempool的策略预估
    minerPolicyEstimator-> (nBlockHeight, entries);
    for (const auto &tx : vtx) {
        txiter it = mapTx.find(tx->GetId());
        if (it != mapTx.end()) {
            setEntries stage;
            stage.insert(it);
            RemoveStaged(stage, true, MemPoolRemovalReason::BLOCK);
        }
        removeConflicts(*tx);
        ClearPrioritisation(tx->GetId());
    }
    lastRollingFeeUpdate = GetTime();
    blockSinceLastRollingFeeBump = true;
}

void CTxMemPool::_clear() {
    mapLinks.clear();
    mapTx.clear();
    mapNextTx.clear();
    vTxHashes.clear();
    totalTxSize = 0;
    cachedInnerUsage = 0;
    lastRollingFeeUpdate = GetTime();
    blockSinceLastRollingFeeBump = false;
    rollingMinimumFeeRate = 0;
    ++nTransactionsUpdated;
}

void CTxMemPool::clear() {
    LOCK(cs);
    _clear();
}

void CTxMemPool::check(const CCoinsViewCache *pcoins) const {
    //查看完整性检查；如果未打开，直接返回。
    if (nCheckFrequency == 0) return;

    if (GetRand(std::numeric_limits<uint32_t>::max()) >= nCheckFrequency)
        return;

    LogPrint("mempool", "Checking mempool with %u transactions and %u inputs\n",
             (unsigned int)mapTx.size(), (unsigned int)mapNextTx.size());

    uint64_t checkTotal = 0;
    uint64_t innerUsage = 0;

    CCoinsViewCache mempoolDuplicate(const_cast<CCoinsViewCache *>(pcoins));
    // 获取当前UTXO集合最高的块索引的 + 1； 即等于本节点接收到下个块的高度。
    const int64_t nSpendHeight = GetSpendHeight(mempoolDuplicate);

    LOCK(cs);

    std::list<const CTxMemPoolEntry *> waitingOnDependants;

    //1. 遍历整个交易池的 所有交易
    for (indexed_transaction_set::const_iterator it = mapTx.begin();
         it != mapTx.end(); it++) {

            unsigned int i = 0;         //累计交易池中所有 交易输入的数量
            checkTotal += it->GetTxSize();
            innerUsage += it->DynamicMemoryUsage();
            const CTransaction &tx = it->GetTx();
            txlinksMap::const_iterator linksiter = mapLinks.find(it);
            assert(linksiter != mapLinks.end());
            const TxLinks &links = linksiter->second;
            innerUsage += memusage::DynamicUsage(links.parents) +
                          memusage::DynamicUsage(links.children);
            bool fDependsWait = false;      //标识交易池中的交易有互相依赖；即存在未花费的交易链。
            setEntries setParentCheck;      //该集合存储这个交易 依赖的交易池中的交易。
            int64_t parentSizes = 0;
            int64_t parentSigOpCount = 0;

            //2. 遍历交易的 每个交易输入；检查该交易的所有交易输入是否在交易池或者UTXO集合中，如果都不在，直接断言出错。
            //同时，判断每个交易的 状态是否与交易池中的jiao正确
            for (const CTxIn &txin : tx.vin) {
                // Check that every mempool transaction's inputs refer to available
                // coins, or other mempool tx's.
                // 检查每个mempool中的交易 要么引用一个有效的 UTXO集合中的UTXO，要么引用了一个在mempool中的交易。
                indexed_transaction_set::const_iterator it2 =
                    mapTx.find(txin.prevout.hash);
                if (it2 != mapTx.end()) {

                    const CTransaction &tx2 = it2->GetTx();
                    assert(tx2.vout.size() > txin.prevout.n &&
                           !tx2.vout[txin.prevout.n].IsNull());
                    fDependsWait = true;            //存在交易依赖链

                    //将这个依赖的交易加入临时集合中，(即:当一个新交易依赖于交易池中的交易时，以它作为父交易，)
                    if (setParentCheck.insert(it2).second) {
                        parentSizes += it2->GetTxSize();
                        parentSigOpCount += it2->GetSigOpCount();
                    }
                } else {
                    //依赖的交易此时必须存在于 UTXO集合中
                    assert(pcoins->HaveCoin(txin.prevout));
                }

                // Check whether its inputs are marked in mapNextTx.
                // 检查是否这个交易输入的引用输出 在交易池的 mapNextTx 结构中。
                auto it3 = mapNextTx.find(txin.prevout);
                assert(it3 != mapNextTx.end());
                assert(it3->first == &txin.prevout);
                assert(it3->second == &tx);
                i++;
            }

            //此时这个集合必须相等，因为它已经存储了这个交易的所有父交易。
            assert(setParentCheck == GetMemPoolParents(it));


            // Verify ancestor state is correct.
            setEntries setAncestors;
            uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
            std::string dummy;
            //3. 获取这个交易的所有祖先交易
            CalculateMemPoolAncestors(*it, setAncestors, nNoLimit, nNoLimit,
                                      nNoLimit, nNoLimit, dummy);
            //4. 累计这个交易的祖先交易 和它的所有状态；查看是否与这个交易本身的记录相等。
            uint64_t nCountCheck = setAncestors.size() + 1;
            uint64_t nSizeCheck = it->GetTxSize();
            Amount nFeesCheck = it->GetModifiedFee();
            int64_t nSigOpCheck = it->GetSigOpCount();
            for (txiter ancestorIt : setAncestors) {
                nSizeCheck += ancestorIt->GetTxSize();
                nFeesCheck += ancestorIt->GetModifiedFee();
                nSigOpCheck += ancestorIt->GetSigOpCount();
            }

            assert(it->GetCountWithAncestors() == nCountCheck);
            assert(it->GetSizeWithAncestors() == nSizeCheck);
            assert(it->GetSigOpCountWithAncestors() == nSigOpCheck);
            assert(it->GetModFeesWithAncestors() == nFeesCheck);

            // Check children against mapNextTx；
            // 检查这个子交易
            CTxMemPool::setEntries setChildrenCheck;        //存储这个交易的子交易
            auto iter = mapNextTx.lower_bound(COutPoint(it->GetTx().GetId(), 0));
            int64_t childSizes = 0;
            for (; iter != mapNextTx.end() &&
                   iter->first->hash == it->GetTx().GetId();
                 ++iter) {
                txiter childit = mapTx.find(iter->second->GetId());
                assert(childit !=
                       mapTx.end()); // mapNextTx points to in-mempool transactions
                if (setChildrenCheck.insert(childit).second) {
                    childSizes += childit->GetTxSize();
                }
            }

            //这个交易的子交易集合必须相等
            assert(setChildrenCheck == GetMemPoolChildren(it));
            // Also check to make sure size is greater than sum with immediate
            // children. Just a sanity check, not definitive that this calc is
            // correct...
            //
            assert(it->GetSizeWithDescendants() >= childSizes + it->GetTxSize());
            //如果这个交易依赖于交易池中的其他交易，将它加入这个集合。
            if (fDependsWait)
                //进入此处的交易，标识该交易有依赖于其他未花费的交易(即在交易池中的交易)
                waitingOnDependants.push_back(&(*it));
            else {
                //进入此处的交易，它的所有交易输入都是直接依赖于UTXO。(即所有依赖的交易都是已经被确定的交易)
                CValidationState state;
                bool fCheckResult = tx.IsCoinBase() ||
                                    Consensus::CheckTxInputs(
                                        tx, state, mempoolDuplicate, nSpendHeight);
                assert(fCheckResult);
                //更新交易池中的交易至UTXO集合
                UpdateCoins(tx, mempoolDuplicate, 1000000);
            }
    }
    unsigned int stepsSinceLastRemove = 0;
    // 遍历所有的依赖于交易池中的 交易
    while (!waitingOnDependants.empty()) {
        const CTxMemPoolEntry *entry = waitingOnDependants.front();
        waitingOnDependants.pop_front();
        CValidationState state;
        // 如果当前节点的UTXO集合中 没有包含该交易的所有引用输入，就将它继续添加至这个链表中
        if (!mempoolDuplicate.HaveInputs(entry->GetTx())) {
            waitingOnDependants.push_back(entry);
            stepsSinceLastRemove++;     //同时这个值继续向后递增
            assert(stepsSinceLastRemove < waitingOnDependants.size());
        } else {
            // UTXO集合包含该交易的所有 引用输入;
            bool fCheckResult =
                entry->GetTx().IsCoinBase() ||
                Consensus::CheckTxInputs(entry->GetTx(), state,
                                         mempoolDuplicate, nSpendHeight);
            assert(fCheckResult);
            //此时会将这个mempool中的交易 更新到UTXO集合的缓存中
            UpdateCoins(entry->GetTx(), mempoolDuplicate, 1000000);
            stepsSinceLastRemove = 0;
        }
    }

    //
    for (auto it = mapNextTx.cbegin(); it != mapNextTx.cend(); it++) {
        // 获取遍历的交易，以及它的ID。
        uint256 txid = it->second->GetId();
        // 根据ID查询 mempool中存储的条目，即判断该交易是否存储在mempool中。
        indexed_transaction_set::const_iterator it2 = mapTx.find(txid);
        // 获取查询到的交易。
        const CTransaction &tx = it2->GetTx();
        assert(it2 != mapTx.end());
        // 判断查询的交易 与 遍历的交易是否为同一个，因为一个交易在交易池中应该只存在一份。
        assert(&tx == it->second);
    }

    assert(totalTxSize == checkTotal);
    assert(innerUsage == cachedInnerUsage);
}

bool CTxMemPool::CompareDepthAndScore(const uint256 &hasha,
                                      const uint256 &hashb) {
    LOCK(cs);
    indexed_transaction_set::const_iterator i = mapTx.find(hasha);
    if (i == mapTx.end()) return false;
    indexed_transaction_set::const_iterator j = mapTx.find(hashb);
    if (j == mapTx.end()) return true;
    uint64_t counta = i->GetCountWithAncestors();
    uint64_t countb = j->GetCountWithAncestors();
    if (counta == countb) {
        return CompareTxMemPoolEntryByScore()(*i, *j);
    }
    return counta < countb;
}

namespace {
class DepthAndScoreComparator {
public:
    bool
    operator()(const CTxMemPool::indexed_transaction_set::const_iterator &a,
               const CTxMemPool::indexed_transaction_set::const_iterator &b) {
        uint64_t counta = a->GetCountWithAncestors();
        uint64_t countb = b->GetCountWithAncestors();
        if (counta == countb) {
            return CompareTxMemPoolEntryByScore()(*a, *b);
        }
        return counta < countb;
    }
};
} // namespace

std::vector<CTxMemPool::indexed_transaction_set::const_iterator>
CTxMemPool::GetSortedDepthAndScore() const {
    std::vector<indexed_transaction_set::const_iterator> iters;
    AssertLockHeld(cs);

    iters.reserve(mapTx.size());

    for (indexed_transaction_set::iterator mi = mapTx.begin();
         mi != mapTx.end(); ++mi) {
        iters.push_back(mi);
    }
    std::sort(iters.begin(), iters.end(), DepthAndScoreComparator());
    return iters;
}

void CTxMemPool::queryHashes(std::vector<uint256> &vtxid) {
    LOCK(cs);
    auto iters = GetSortedDepthAndScore();

    vtxid.clear();
    vtxid.reserve(mapTx.size());

    for (auto it : iters) {
        vtxid.push_back(it->GetTx().GetId());
    }
}

static TxMempoolInfo
GetInfo(CTxMemPool::indexed_transaction_set::const_iterator it) {
    return TxMempoolInfo{it->GetSharedTx(), it->GetTime(),
                         CFeeRate(it->GetFee(), it->GetTxSize()),
                         it->GetModifiedFee() - it->GetFee()};
}

std::vector<TxMempoolInfo> CTxMemPool::infoAll() const {
    LOCK(cs);
    auto iters = GetSortedDepthAndScore();

    std::vector<TxMempoolInfo> ret;
    ret.reserve(mapTx.size());
    for (auto it : iters) {
        ret.push_back(GetInfo(it));
    }

    return ret;
}

CTransactionRef CTxMemPool::get(const uint256 &txid) const {
    LOCK(cs);
    indexed_transaction_set::const_iterator i = mapTx.find(txid);
    if (i == mapTx.end()) return nullptr;
    return i->GetSharedTx();
}

TxMempoolInfo CTxMemPool::info(const uint256 &txid) const {
    LOCK(cs);
    indexed_transaction_set::const_iterator i = mapTx.find(txid);
    if (i == mapTx.end()) return TxMempoolInfo();
    return GetInfo(i);
}

CFeeRate CTxMemPool::estimateFee(int nBlocks) const {
    LOCK(cs);
    return minerPolicyEstimator->estimateFee(nBlocks);
}
CFeeRate CTxMemPool::estimateSmartFee(int nBlocks,
                                      int *answerFoundAtBlocks) const {
    LOCK(cs);
    return minerPolicyEstimator->estimateSmartFee(nBlocks, answerFoundAtBlocks,
                                                  *this);
}
double CTxMemPool::estimatePriority(int nBlocks) const {
    LOCK(cs);
    return minerPolicyEstimator->estimatePriority(nBlocks);
}
double CTxMemPool::estimateSmartPriority(int nBlocks,
                                         int *answerFoundAtBlocks) const {
    LOCK(cs);
    return minerPolicyEstimator->estimateSmartPriority(
        nBlocks, answerFoundAtBlocks, *this);
}

bool CTxMemPool::WriteFeeEstimates(CAutoFile &fileout) const {
    try {
        LOCK(cs);
        // version required to read: 0.13.99 or later
        fileout << 139900;
        // version that wrote the file
        fileout << CLIENT_VERSION;
        minerPolicyEstimator->Write(fileout);
    } catch (const std::exception &) {
        LogPrintf("CTxMemPool::WriteFeeEstimates(): unable to write policy "
                  "estimator data (non-fatal)\n");
        return false;
    }
    return true;
}

bool CTxMemPool::ReadFeeEstimates(CAutoFile &filein) {
    try {
        int nVersionRequired, nVersionThatWrote;
        filein >> nVersionRequired >> nVersionThatWrote;
        if (nVersionRequired > CLIENT_VERSION)
            return error("CTxMemPool::ReadFeeEstimates(): up-version (%d) fee "
                         "estimate file",
                         nVersionRequired);
        LOCK(cs);
        minerPolicyEstimator->Read(filein, nVersionThatWrote);
    } catch (const std::exception &) {
        LogPrintf("CTxMemPool::ReadFeeEstimates(): unable to read policy "
                  "estimator data (non-fatal)\n");
        return false;
    }
    return true;
}

// 修改 优先交易；
void CTxMemPool::PrioritiseTransaction(const uint256 hash,
                                       const std::string strHash,
                                       double dPriorityDelta,
                                       const Amount nFeeDelta) {
    {
        LOCK(cs);
        //1. 此处开始对 mapDeltas 中的交易 进行赋值。利用C++的map 查找特性，
        std::pair<double, Amount> &deltas = mapDeltas[hash];
        deltas.first += dPriorityDelta;
        deltas.second += nFeeDelta;
        // 查找交易池中的这个交易。
        txiter it = mapTx.find(hash);
        if (it != mapTx.end()) {
            mapTx.modify(it, update_fee_delta(deltas.second));
            // Now update all ancestors' modified fees with descendants
            setEntries setAncestors;
            uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
            std::string dummy;
            CalculateMemPoolAncestors(*it, setAncestors, nNoLimit, nNoLimit,
                                      nNoLimit, nNoLimit, dummy, false);
            for (txiter ancestorIt : setAncestors) {
                mapTx.modify(ancestorIt,
                             update_descendant_state(0, nFeeDelta, 0));
            }
            // Now update all descendants' modified fees with ancestors
            setEntries setDescendants;
            CalculateDescendants(it, setDescendants);
            setDescendants.erase(it);
            for (txiter descendantIt : setDescendants) {
                mapTx.modify(descendantIt,
                             update_ancestor_state(0, nFeeDelta, 0, 0));
            }
        }
    }
    LogPrintf("PrioritiseTransaction: %s priority += %f, fee += %d\n", strHash,
              dPriorityDelta, FormatMoney(nFeeDelta));
}

// 如果交易池中已存在该交易，获取交易在交易池中的交易费和优先级; 否则退出。
// hash(in): 该交易的哈希； nFeeDelta(out):一个交易的交易费。dPriorityDelta(out):传出值，依据交易费算出的优先级
void CTxMemPool::ApplyDeltas(const uint256 hash, double &dPriorityDelta,
                             Amount &nFeeDelta) const {
    LOCK(cs);
    std::map<uint256, std::pair<double, Amount>>::const_iterator pos =
        mapDeltas.find(hash);
    if (pos == mapDeltas.end()) return;
    const std::pair<double, Amount> &deltas = pos->second;
    dPriorityDelta += deltas.first;
    nFeeDelta += deltas.second;
}

void CTxMemPool::ClearPrioritisation(const uint256 hash) {
    LOCK(cs);
    mapDeltas.erase(hash);
}

// 交易池含有该交易中的某个引用交易时，返回false； 都不存在时，返回TRUE。
bool CTxMemPool::HasNoInputsOf(const CTransaction &tx) const {
    for (unsigned int i = 0; i < tx.vin.size(); i++)
        if (exists(tx.vin[i].prevout.hash)) return false;
    return true;
}

CCoinsViewMemPool::CCoinsViewMemPool(CCoinsView *baseIn,
                                     const CTxMemPool &mempoolIn)
    : CCoinsViewBacked(baseIn), mempool(mempoolIn) {}

//先查找矿池中是否有该outpoint，如果没有，再查UTXO集合中是否有该outpoint
bool CCoinsViewMemPool::GetCoin(const COutPoint &outpoint, Coin &coin) const {
    // If an entry in the mempool exists, always return that one, as it's
    // guaranteed to never conflict with the underlying cache, and it cannot
    // have pruned entries (as it contains full) transactions. First checking
    // the underlying cache risks returning a pruned entry instead.
    // 1. 从mempool中去获取该哈希所表示的交易，
    CTransactionRef ptx = mempool.get(outpoint.hash);
    // 2. 看查找的交易是否在交易池中，如果存在
    if (ptx) {
        //3. 判断该preOut是否合理，如果合理，构建该preOut所对应的coin，将它返回。
        if (outpoint.n < ptx->vout.size()) {
            coin = Coin(ptx->vout[outpoint.n], MEMPOOL_HEIGHT, false);
            return true;
        }
        return false;
    }

    return base->GetCoin(outpoint, coin) && !coin.IsSpent();
}

//查看mempool或UTXO中是否有该交易输出
bool CCoinsViewMemPool::HaveCoin(const COutPoint &outpoint) const {
    return mempool.exists(outpoint) || base->HaveCoin(outpoint);
}

// 预估当前交易池的内存消耗大小
size_t CTxMemPool::DynamicMemoryUsage() const {
    LOCK(cs);
    // Estimate the overhead of mapTx to be 15 pointers + an allocation, as no
    // exact formula for boost::multi_index_contained is implemented.
    return memusage::MallocUsage(sizeof(CTxMemPoolEntry) +
                                 15 * sizeof(void *)) *
               mapTx.size() +
           memusage::DynamicUsage(mapNextTx) +
           memusage::DynamicUsage(mapDeltas) +
           memusage::DynamicUsage(mapLinks) +
           memusage::DynamicUsage(vTxHashes) + cachedInnerUsage;
}

// 从交易池中移除这个集合中的所有交易。此时不需要更新后代交易，因为所有这个集合中，所有的后代交易都被删除了。
// stage(in/out):删除交易的集合； updateDescendants(in):是否更新这些删除交易的后代交易的祖先状态；
// reason(in):删除的原因
void CTxMemPool::RemoveStaged(setEntries &stage, bool updateDescendants,
                              MemPoolRemovalReason reason) {
    AssertLockHeld(cs);
    UpdateForRemoveFromMempool(stage, updateDescendants);
    for (const txiter &it : stage) {
        removeUnchecked(it, reason);
    }
}

//移除 这个时间之前进入交易的交易
int CTxMemPool::Expire(int64_t time) {
    LOCK(cs);
    indexed_transaction_set::index<entry_time>::type::iterator it =
        mapTx.get<entry_time>().begin();
    setEntries toremove;
    //1. 从最早的时间交易开始遍历，且当该交易的时间小于删除时间时，将这个将要删除的交易加入集合中。
    while (it != mapTx.get<entry_time>().end() && it->GetTime() < time) {
        toremove.insert(mapTx.project<0>(it));
        it++;
    }

    //2. 统计这些要删除交易的所有后代交易。
    setEntries stage;
    for (txiter removeit : toremove) {
        CalculateDescendants(removeit, stage);
    }

    //3. 移除这些交易。
    RemoveStaged(stage, false, MemPoolRemovalReason::EXPIRY);
    //4. 返回移除交易的数量
    return stage.size();
}

//添加交易至交易池。validFeeEstimate(in): 有效的交易费预估。entry(in):交易池条目。hash(in):该交易池的
bool CTxMemPool::addUnchecked(const uint256 &hash, const CTxMemPoolEntry &entry,
                              bool validFeeEstimate) {
    LOCK(cs);
    setEntries setAncestors;
    uint64_t nNoLimit = std::numeric_limits<uint64_t>::max();
    std::string dummy;
    CalculateMemPoolAncestors(entry, setAncestors, nNoLimit, nNoLimit, nNoLimit,
                              nNoLimit, dummy);
    return addUnchecked(hash, entry, setAncestors, validFeeEstimate);
}

void CTxMemPool::UpdateChild(txiter entry, txiter child, bool add) {
    setEntries s;
    if (add && mapLinks[entry].children.insert(child).second) {
        cachedInnerUsage += memusage::IncrementalDynamicUsage(s);
    } else if (!add && mapLinks[entry].children.erase(child)) {
        cachedInnerUsage -= memusage::IncrementalDynamicUsage(s);
    }
}

// 更新参一的子交易的 父交易相关的信息； 根据参三：是添加还是删除该父交易
// entry(in) : 将要更新的子交易；  parent(in) : 该子交易的父交易；
// add(in): TRUE，向该子交易的父交易集合添加它的父交易； false,删除这个父交易
void CTxMemPool::UpdateParent(txiter entry, txiter parent, bool add) {
    setEntries s;
    if (add && mapLinks[entry].parents.insert(parent).second) {
        //此处是更新交易池的内存消耗。因为这块的设计是：一个交易的父交易集合和子交易集合都是放在交易池中的。
        // 所以此处 向父交易集合添加或删除元素， 需要更新交易池的内存。
        // 在自己的设计中，需要增加这块的消耗
        cachedInnerUsage += memusage::IncrementalDynamicUsage(s);
    } else if (!add && mapLinks[entry].parents.erase(parent)) {
        cachedInnerUsage -= memusage::IncrementalDynamicUsage(s);
    }
}

const CTxMemPool::setEntries &
CTxMemPool::GetMemPoolParents(txiter entry) const {
    assert(entry != mapTx.end());
    txlinksMap::const_iterator it = mapLinks.find(entry);
    assert(it != mapLinks.end());
    return it->second.parents;
}

const CTxMemPool::setEntries &
CTxMemPool::GetMemPoolChildren(txiter entry) const {
    assert(entry != mapTx.end());
    txlinksMap::const_iterator it = mapLinks.find(entry);
    assert(it != mapLinks.end());
    return it->second.children;
}

// 获取交易池的指定最低费率； 根据传入的交易池的字节限制
CFeeRate CTxMemPool::GetMinFee(size_t sizelimit) const {
    LOCK(cs);
    if (!blockSinceLastRollingFeeBump || rollingMinimumFeeRate == 0)
        return CFeeRate(Amount(int64_t(rollingMinimumFeeRate)));

    int64_t time = GetTime();

    // 每隔最少 10s 才可以去更新一次手续费； 此时可能有一次0手续费
    if (time > lastRollingFeeUpdate + 10) {
        double halflife = ROLLING_FEE_HALFLIFE;     //12小时
        // 如果当前交易池的消耗 < 指定的1/4; 则更新半周期为 1/4
        if (DynamicMemoryUsage() < sizelimit / 4)
            halflife /= 4;
        else if (DynamicMemoryUsage() < sizelimit / 2)
        // 如果当前的交易池消耗 < 指定的 1/2;则更新半周期为 1/2
            halflife /= 2;

        // 更新进入矿池的最低手续费率 和 更新手续费的时间
        rollingMinimumFeeRate =
            rollingMinimumFeeRate /
            pow(2.0, (time - lastRollingFeeUpdate) / halflife);
        lastRollingFeeUpdate = time;        //最后一次更新矿池手续费的时间

        //如果最低的手续费率小于 指定的1/2;则将最低的手续费率赋值为0；返回此时进入矿池的手续费为0.
        if (rollingMinimumFeeRate <
            (double)incrementalRelayFee.GetFeePerK().GetSatoshis() / 2) {
            rollingMinimumFeeRate = 0;
            return CFeeRate(0);
        }
    }

    // 不处于更新状态时，直接返回矿池手续费。
    return std::max(CFeeRate(Amount(int64_t(rollingMinimumFeeRate))),
                    incrementalRelayFee);
}

void CTxMemPool::trackPackageRemoved(const CFeeRate &rate) {
    AssertLockHeld(cs);
    if (rate.GetFeePerK().GetSatoshis() > rollingMinimumFeeRate) {
        rollingMinimumFeeRate = rate.GetFeePerK().GetSatoshis();
        blockSinceLastRollingFeeBump = false;
    }
}

//限制交易池的大小； sizelimit(in):交易池的限制大小；
//pvNoSpendsRemaining(out):
void CTxMemPool::TrimToSize(size_t sizelimit,
                            std::vector<COutPoint> *pvNoSpendsRemaining) {
    LOCK(cs);

    unsigned nTxnRemoved = 0;
    CFeeRate maxFeeRateRemoved(0);
    while (!mapTx.empty() && DynamicMemoryUsage() > sizelimit) {
        indexed_transaction_set::index<descendant_score>::type::iterator it =
            mapTx.get<descendant_score>().begin();

        // We set the new mempool min fee to the feerate of the removed set,
        // plus the "minimum reasonable fee rate" (ie some value under which we
        // consider txn to have 0 fee). This way, we don't allow txn to enter
        // mempool with feerate equal to txn which were removed with no block in
        // between.
        CFeeRate removed(it->GetModFeesWithDescendants(),
                         it->GetSizeWithDescendants());
        removed += incrementalRelayFee;
        trackPackageRemoved(removed);
        maxFeeRateRemoved = std::max(maxFeeRateRemoved, removed);

        setEntries stage;
        CalculateDescendants(mapTx.project<0>(it), stage);
        nTxnRemoved += stage.size();

        std::vector<CTransaction> txn;
        if (pvNoSpendsRemaining) {
            txn.reserve(stage.size());
            for (txiter iter : stage) {
                txn.push_back(iter->GetTx());
            }
        }
        RemoveStaged(stage, false, MemPoolRemovalReason::SIZELIMIT);
        if (pvNoSpendsRemaining) {
            for (const CTransaction &tx : txn) {
                for (const CTxIn &txin : tx.vin) {
                    if (exists(txin.prevout.hash)) {
                        continue;
                    }
                    if (!mapNextTx.count(txin.prevout)) {
                        pvNoSpendsRemaining->push_back(txin.prevout);
                    }
                }
            }
        }
    }

    if (maxFeeRateRemoved > CFeeRate(0))
        LogPrint("mempool",
                 "Removed %u txn, rolling minimum fee bumped to %s\n",
                 nTxnRemoved, maxFeeRateRemoved.ToString());
}

bool CTxMemPool::TransactionWithinChainLimit(const uint256 &txid,
                                             size_t chainLimit) const {
    LOCK(cs);
    auto it = mapTx.find(txid);
    return it == mapTx.end() || (it->GetCountWithAncestors() < chainLimit &&
                                 it->GetCountWithDescendants() < chainLimit);
}

SaltedTxidHasher::SaltedTxidHasher()
    : k0(GetRand(std::numeric_limits<uint64_t>::max())),
      k1(GetRand(std::numeric_limits<uint64_t>::max())) {}
