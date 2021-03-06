// Copyright (c) 2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "amount.h"
#include "base58.h"
#include "chain.h"
#include "chainparams.h"
#include "config.h"
#include "consensus/consensus.h"
#include "consensus/params.h"
#include "consensus/validation.h"
#include "core_io.h"
#include "init.h"
#include "miner.h"
#include "net.h"
#include "policy/policy.h"
#include "pow.h"
#include "rpc/blockchain.h"
#include "rpc/server.h"
#include "txmempool.h"
#include "util.h"
#include "utilstrencodings.h"
#include "validation.h"
#include "validationinterface.h"
#include "../validation.h"
#include "server.h"
#include "../chainparams.h"
#include "../policy/policy.h"
#include "../miner.h"
#include "../utiltime.h"
#include "protocol.h"
#include "../core_io.h"
#include "../consensus/consensus.h"
#include "../validationinterface.h"
#include "../script/standard.h"

#include <univalue.h>

#include <cstdint>
#include <memory>

/**
 * Return average network hashes per second based on the last 'lookup' blocks,
 * or from the last difficulty change if 'lookup' is nonpositive. If 'height' is
 * nonnegative, compute the estimate at the time when a given block was found.
 */
// 返回基于最新发现的块每秒的平均网络哈希，或若发现是非正则返回最新的难度改变。若高度非负，计算找到一个给定区块时的估计值
static UniValue GetNetworkHashPS(int lookup, int height) { // 默认 (120, -1)
    CBlockIndex *pb = chainActive.Tip();// 获取链尖区块索引

    if (height >= 0 && height < chainActive.Height()) {// 若指定高度符合当前链高度范围
        pb = chainActive[height]; // 获取对应高度的区块索引
    }

    if (pb == nullptr || !pb->nHeight) {// 索引为空 或 为创世区块索引
        return 0;
    }

    // If lookup is -1, then use blocks since last difficulty change.
    if (lookup <= 0) {// 若发现是 -1，则使用从上次难度改变后的区块
        lookup = pb->nHeight %
                     Params().GetConsensus().DifficultyAdjustmentInterval() +
                 1;
    }

    // If lookup is larger than chain, then set it to chain length.
    if (lookup > pb->nHeight) {// 若发现大于链高度，则设置为链高度
        lookup = pb->nHeight;
    }

    CBlockIndex *pb0 = pb;
    int64_t minTime = pb0->GetBlockTime();
    int64_t maxTime = minTime;
    for (int i = 0; i < lookup; i++) {
        pb0 = pb0->pprev;
        int64_t time = pb0->GetBlockTime();
        minTime = std::min(time, minTime);
        maxTime = std::max(time, maxTime);// 获取最小创建区块时间
    }

    // In case there's a situation where minTime == maxTime, we don't want a
    // divide by zero exception.
    if (minTime == maxTime) {// 最小和最大不能相等
        return 0;
    }

    arith_uint256 workDiff = pb->nChainWork - pb0->nChainWork;// 区间首尾区块的工作量之差
    int64_t timeDiff = maxTime - minTime;// 时间差

    return workDiff.getdouble() / timeDiff;// 转换为浮点数求平均值并返回
}

//获取基于最后 n 个区块估算的网络算力（每秒网络哈希次数）
//（数字）返回估算的每秒网络哈希的次数（链工作量 chainwork 之差 / 时间 time 之差）

//基本流程：
//1.处理命令帮助和参数个数。
//2.上锁。
//3.获取指定高度及块数的算力（网络哈希/秒），并返回。
static UniValue getnetworkhashps(const Config &config,
                                 const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() > 2) {// 参数个数最多为 2 个
        throw std::runtime_error(
            "getnetworkhashps ( nblocks "//整型，可选，默认为 120）区块的数量，-1 表示从上一次变化的难度开始。
                    "height )\n"//整型，可选，默认为 -1 表示当前高度）给定区块链高度用于评估当某个块被找到时的网络速度。
            "\nReturns the estimated network hashes per second based on the "
            "last n blocks.\n"
            "Pass in [blocks] to override # of blocks, -1 specifies since last "
            "difficulty change.\n"
            "Pass in [height] to estimate the network speed at the time when a "
            "certain block was found.\n"
            "\nArguments:\n"
            "1. nblocks     (numeric, optional, default=120) The number of "
            "blocks, or -1 for blocks since last difficulty change.\n"
            "2. height      (numeric, optional, default=-1) To estimate at the "
            "time of the given height.\n"
            "\nResult:\n"
            "x             (numeric) Hashes per second estimated\n"
            "\nExamples:\n" +
            HelpExampleCli("getnetworkhashps", "") +
            HelpExampleRpc("getnetworkhashps", ""));
    }

    LOCK(cs_main);
    return GetNetworkHashPS(
        request.params.size() > 0 ? request.params[0].get_int() : 120,
        request.params.size() > 1 ? request.params[1].get_int() : -1);
}

static UniValue generateBlocks(const Config &config,
                               std::shared_ptr<CReserveScript> coinbaseScript,
                               int nGenerate, uint64_t nMaxTries,
                               bool keepScript) {
    static const int nInnerLoopCount = 0x100000;
    int nHeightStart = 0;// 产生块前的高度
    int nHeightEnd = 0;// 产生块后的高度
    int nHeight = 0;// 当前区块链高度

    {
        // Don't keep cs_main locked.
        LOCK(cs_main);// 缩小加锁的范围
        nHeightStart = chainActive.Height();// 7.获取当前激活链高度
        nHeight = nHeightStart;// 记录当前高度
        nHeightEnd = nHeightStart + nGenerate;// 得到产生指定块数后的高度
    }

    unsigned int nExtraNonce = 0;
    UniValue blockHashes(UniValue::VARR);// 数组类型的区块哈希对象
    while (nHeight < nHeightEnd) {// 8.循环产生指定数目的区块
        std::unique_ptr<CBlockTemplate> pblocktemplate(// 8.1.创建区块模板
            BlockAssembler(config, Params())
                .CreateNewBlock(coinbaseScript->reserveScript));
        if (!pblocktemplate.get()) {// 8.2.验证是否创建成功
            throw JSONRPCError(RPC_INTERNAL_ERROR, "Couldn't create new block");
        }
        CBlock *pblock = &pblocktemplate->block;// 获取区块指针
        {
            LOCK(cs_main);
            IncrementExtraNonce(config, pblock, chainActive.Tip(), nExtraNonce);// 8.3.增加额外的随机数
        }
        while (nMaxTries > 0 && pblock->nNonce < nInnerLoopCount &&// 8.4.检测区块是否满足工作量证明
               !CheckProofOfWork(pblock->GetHash(), pblock->nBits,
                                 Params().GetConsensus())) {
            ++pblock->nNonce;// 区块头内随机数加 1
            --nMaxTries;
        }
        if (nMaxTries == 0) {
            break;
        }
        if (pblock->nNonce == nInnerLoopCount) {
            continue;
        }
        std::shared_ptr<const CBlock> shared_pblock =
            std::make_shared<const CBlock>(*pblock);
        if (!ProcessNewBlock(config, shared_pblock, true, nullptr)) {
            throw JSONRPCError(RPC_INTERNAL_ERROR,
                               "ProcessNewBlock, block not accepted");
        }
        ++nHeight; // 增加当前高度
        blockHashes.push_back(pblock->GetHash().GetHex());

        // Mark script as important because it was used at least for one
        // coinbase output if the script came from the wallet.
        if (keepScript) {
            coinbaseScript->KeepScript();// 8.7.标记该脚本为重要，因为它至少用作一个创币输出
        }
    }

    return blockHashes;// 9.返回产生所有区块的哈希
}

//立刻挖出区块（在 RPC 调用返回前）
//此功能仅限回归测试网 regtest 使用。
static UniValue generate(const Config &config, const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() < 1 ||
        request.params.size() > 2) {// 1.参数只能为 1 个（要生成区块的个数
        throw std::runtime_error(
            "generate nblocks ( maxtries )\n"
            "\nMine up to nblocks blocks immediately (before the RPC call "
            "returns)\n"
            "\nArguments:\n"
            "1. nblocks      (numeric, required) How many blocks are generated "
            "immediately.\n"
            "2. maxtries     (numeric, optional) How many iterations to try "
            "(default = 1000000).\n"
            "\nResult:\n"
            "[ blockhashes ]     (array) hashes of blocks generated\n"
            "\nExamples:\n"
            "\nGenerate 11 blocks\n" +
            HelpExampleCli("generate", "11"));
    }

    int nGenerate = request.params[0].get_int();// 3.获取要产生区块的数目
    uint64_t nMaxTries = 1000000;
    if (request.params.size() > 1) {
        nMaxTries = request.params[1].get_int();
    }

    std::shared_ptr<CReserveScript> coinbaseScript;// 4.创建创币交易脚本
    GetMainSignals().ScriptForMining(coinbaseScript);

    // If the keypool is exhausted, no script is returned at all. Catch this.
    if (!coinbaseScript) {// 5.若密钥池耗尽，根本不会返回脚本。抓住它
        throw JSONRPCError(
            RPC_WALLET_KEYPOOL_RAN_OUT,
            "Error: Keypool ran out, please call keypoolrefill first");
    }

    // Throw an error if no script was provided.
    if (coinbaseScript->reserveScript.empty()) {// 6.如果脚本为空，未被提供，则抛出一个错误
        throw JSONRPCError(
            RPC_INTERNAL_ERROR,
            "No coinbase script available (mining requires a wallet)");
    }

    return generateBlocks(config, coinbaseScript, nGenerate, nMaxTries, true);
}

static UniValue generatetoaddress(const Config &config,
                                  const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() < 2 ||
        request.params.size() > 3) {
        throw std::runtime_error(
            "generatetoaddress nblocks address (maxtries)\n"
            "\nMine blocks immediately to a specified address (before the RPC "
            "call returns)\n"
            "\nArguments:\n"
            "1. nblocks      (numeric, required) How many blocks are generated "
            "immediately.\n"
            "2. address      (string, required) The address to send the newly "
            "generated bitcoin to.\n"
            "3. maxtries     (numeric, optional) How many iterations to try "
            "(default = 1000000).\n"
            "\nResult:\n"
            "[ blockhashes ]     (array) hashes of blocks generated\n"
            "\nExamples:\n"
            "\nGenerate 11 blocks to myaddress\n" +
            HelpExampleCli("generatetoaddress", "11 \"myaddress\""));
    }

    int nGenerate = request.params[0].get_int();
    uint64_t nMaxTries = 1000000;
    if (request.params.size() > 2) {
        nMaxTries = request.params[2].get_int();
    }

    CTxDestination destination = DecodeDestination(request.params[1].get_str());
    if (!IsValidDestination(destination)) {
        throw JSONRPCError(RPC_INVALID_ADDRESS_OR_KEY,
                           "Error: Invalid address");
    }

    std::shared_ptr<CReserveScript> coinbaseScript(new CReserveScript());
    coinbaseScript->reserveScript = GetScriptForDestination(destination);

    return generateBlocks(config, coinbaseScript, nGenerate, nMaxTries, false);
}

static UniValue getmininginfo(const Config &config,
                              const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() != 0) {
        throw std::runtime_error(
            "getmininginfo\n"
            "\nReturns a json object containing mining-related information."
            "\nResult:\n"
            "{\n"
            "  \"blocks\": nnn,             (numeric) The current block\n"
            "  \"currentblocksize\": nnn,   (numeric) The last block size\n"
            "  \"currentblocktx\": nnn,     (numeric) The last block "
            "transaction\n"
            "  \"difficulty\": xxx.xxxxx    (numeric) The current difficulty\n"
            "  \"errors\": \"...\"            (string) Current errors\n"
            "  \"networkhashps\": nnn,      (numeric) The network hashes per "
            "second\n"
            "  \"pooledtx\": n              (numeric) The size of the mempool\n"
            "  \"chain\": \"xxxx\",           (string) current network name as "
            "defined in BIP70 (main, test, regtest)\n"
            "}\n"
            "\nExamples:\n" +
            HelpExampleCli("getmininginfo", "") +
            HelpExampleRpc("getmininginfo", ""));
    }

    LOCK(cs_main);

    UniValue obj(UniValue::VOBJ);
    obj.push_back(Pair("blocks", int(chainActive.Height())));
    obj.push_back(Pair("currentblocksize", uint64_t(nLastBlockSize)));
    obj.push_back(Pair("currentblocktx", uint64_t(nLastBlockTx)));
    obj.push_back(Pair("difficulty", double(GetDifficulty(chainActive.Tip()))));
    obj.push_back(Pair("blockprioritypercentage",
                       uint8_t(GetArg("-blockprioritypercentage",
                                      DEFAULT_BLOCK_PRIORITY_PERCENTAGE))));
    obj.push_back(Pair("errors", GetWarnings("statusbar")));
    obj.push_back(Pair("networkhashps", getnetworkhashps(config, request)));
    obj.push_back(Pair("pooledtx", uint64_t(mempool.size())));
    obj.push_back(Pair("chain", Params().NetworkIDString()));
    return obj;
}

// NOTE: Unlike wallet RPC (which use BCC values), mining RPCs follow GBT (BIP
// 22) in using satoshi amounts
static UniValue prioritisetransaction(const Config &config,
                                      const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() != 3) {
        throw std::runtime_error(
            "prioritisetransaction <txid> <priority delta> <fee delta>\n"
            "Accepts the transaction into mined blocks at a higher (or lower) "
            "priority\n"
            "\nArguments:\n"
            "1. \"txid\"       (string, required) The transaction id.\n"
            "2. priority_delta (numeric, required) The priority to add or "
            "subtract.\n"
            "                  The transaction selection algorithm considers "
            "the tx as it would have a higher priority.\n"
            "                  (priority of a transaction is calculated: "
            "coinage * value_in_satoshis / txsize) \n"
            "3. fee_delta      (numeric, required) The fee value (in satoshis) "
            "to add (or subtract, if negative).\n"
            "                  The fee is not actually paid, only the "
            "algorithm for selecting transactions into a block\n"
            "                  considers the transaction as it would have paid "
            "a higher (or lower) fee.\n"
            "\nResult:\n"
            "true              (boolean) Returns true\n"
            "\nExamples:\n" +
            HelpExampleCli("prioritisetransaction", "\"txid\" 0.0 10000") +
            HelpExampleRpc("prioritisetransaction", "\"txid\", 0.0, 10000"));
    }

    LOCK(cs_main);

    uint256 hash = ParseHashStr(request.params[0].get_str(), "txid");
    CAmount nAmount = request.params[2].get_int64();

    mempool.PrioritiseTransaction(hash, request.params[0].get_str(),
                                  request.params[1].get_real(), nAmount);
    return true;
}

// NOTE: Assumes a conclusive result; if result is inconclusive, it must be
// handled by caller
static UniValue BIP22ValidationResult(const Config &config,
                                      const CValidationState &state) {
    if (state.IsValid()) {
        return NullUniValue;
    }

    std::string strRejectReason = state.GetRejectReason();
    if (state.IsError()) {
        throw JSONRPCError(RPC_VERIFY_ERROR, strRejectReason);
    }

    if (state.IsInvalid()) {
        if (strRejectReason.empty()) {
            return "rejected";
        }
        return strRejectReason;
    }

    // Should be impossible.
    return "valid?";
}

std::string gbt_vb_name(const Consensus::DeploymentPos pos) {
    const struct BIP9DeploymentInfo &vbinfo = VersionBitsDeploymentInfo[pos];
    std::string s = vbinfo.name;
    if (!vbinfo.gbt_force) {
        s.insert(s.begin(), '!');
    }
    return s;
}

//如果请求参数包含 mode 关键字，用于在默认的 template 请求或 proposal 间选择。 返回构建一个区块所需的数据。
//获取区块模板
//基本流程：
//1.处理命令帮助和参数个数。
//2.上锁。
//3.获取指定参数。
//4.根据参数创建新区块模板。
//5.获取区块模板相关信息并返回。
static UniValue getblocktemplate(const Config &config,
                                 const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() > 1) {// 参数最多为 1 个
        throw std::runtime_error(
            "getblocktemplate ( TemplateRequest )\n"
            "\nIf the request parameters include a 'mode' key, that is used to "
            "explicitly select between the default 'template' request or a "
            "'proposal'.\n"
            "It returns data needed to construct a block to work on.\n"
            "For full specification, see BIPs 22, 23, 9, and 145:\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/bip-0022.mediawiki\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/bip-0023.mediawiki\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/"
            "bip-0009.mediawiki#getblocktemplate_changes\n"
            "    "
            "https://github.com/bitcoin/bips/blob/master/bip-0145.mediawiki\n"

            "\nArguments:\n"
            "1. template_request         (json object, optional) A json object "
            "in the following spec\n"
            "     {\n"
            "       \"mode\":\"template\"    (string, optional) This must be "
            "set to \"template\", \"proposal\" (see BIP 23), or omitted\n"
            "       \"capabilities\":[     (array, optional) A list of "
            "strings\n"
            "           \"support\"          (string) client side supported "
            "feature, 'longpoll', 'coinbasetxn', 'coinbasevalue', 'proposal', "
            "'serverlist', 'workid'\n"
            "           ,...\n"
            "       ],\n"
            "       \"rules\":[            (array, optional) A list of "
            "strings\n"
            "           \"support\"          (string) client side supported "
            "softfork deployment\n"
            "           ,...\n"
            "       ]\n"
            "     }\n"
            "\n"

            "\nResult:\n"
            "{\n"
            "  \"version\" : n,                    (numeric) The preferred "
            "block version\n"
            "  \"rules\" : [ \"rulename\", ... ],    (array of strings) "
            "specific block rules that are to be enforced\n"
            "  \"vbavailable\" : {                 (json object) set of "
            "pending, supported versionbit (BIP 9) softfork deployments\n"
            "      \"rulename\" : bitnumber          (numeric) identifies the "
            "bit number as indicating acceptance and readiness for the named "
            "softfork rule\n"
            "      ,...\n"
            "  },\n"
            "  \"vbrequired\" : n,                 (numeric) bit mask of "
            "versionbits the server requires set in submissions\n"
            "  \"previousblockhash\" : \"xxxx\",     (string) The hash of "
            "current highest block\n"
            "  \"transactions\" : [                (array) contents of "
            "non-coinbase transactions that should be included in the next "
            "block\n"
            "      {\n"
            "         \"data\" : \"xxxx\",             (string) transaction "
            "data encoded in hexadecimal (byte-for-byte)\n"
            "         \"txid\" : \"xxxx\",             (string) transaction id "
            "encoded in little-endian hexadecimal\n"
            "         \"hash\" : \"xxxx\",             (string) hash encoded "
            "in little-endian hexadecimal (including witness data)\n"
            "         \"depends\" : [                (array) array of numbers "
            "\n"
            "             n                          (numeric) transactions "
            "before this one (by 1-based index in 'transactions' list) that "
            "must be present in the final block if this one is\n"
            "             ,...\n"
            "         ],\n"
            "         \"fee\": n,                    (numeric) difference in "
            "value between transaction inputs and outputs (in Satoshis); for "
            "coinbase transactions, this is a negative Number of the total "
            "collected block fees (ie, not including the block subsidy); if "
            "key is not present, fee is unknown and clients MUST NOT assume "
            "there isn't one\n"
            "         \"sigops\" : n,                (numeric) total SigOps "
            "cost, as counted for purposes of block limits; if key is not "
            "present, sigop cost is unknown and clients MUST NOT assume it is "
            "zero\n"
            "         \"required\" : true|false      (boolean) if provided and "
            "true, this transaction must be in the final block\n"
            "      }\n"
            "      ,...\n"
            "  ],\n"
            "  \"coinbaseaux\" : {                 (json object) data that "
            "should be included in the coinbase's scriptSig content\n"
            "      \"flags\" : \"xx\"                  (string) key name is to "
            "be ignored, and value included in scriptSig\n"
            "  },\n"
            "  \"coinbasevalue\" : n,              (numeric) maximum allowable "
            "input to coinbase transaction, including the generation award and "
            "transaction fees (in Satoshis)\n"
            "  \"coinbasetxn\" : { ... },          (json object) information "
            "for coinbase transaction\n"
            "  \"target\" : \"xxxx\",                (string) The hash target\n"
            "  \"mintime\" : xxx,                  (numeric) The minimum "
            "timestamp appropriate for next block time in seconds since epoch "
            "(Jan 1 1970 GMT)\n"
            "  \"mutable\" : [                     (array of string) list of "
            "ways the block template may be changed \n"
            "     \"value\"                          (string) A way the block "
            "template may be changed, e.g. 'time', 'transactions', "
            "'prevblock'\n"
            "     ,...\n"
            "  ],\n"
            "  \"noncerange\" : \"00000000ffffffff\",(string) A range of valid "
            "nonces\n"
            "  \"sigoplimit\" : n,                 (numeric) limit of sigops "
            "in blocks\n"
            "  \"sizelimit\" : n,                  (numeric) limit of block "
            "size\n"
            "  \"curtime\" : ttt,                  (numeric) current timestamp "
            "in seconds since epoch (Jan 1 1970 GMT)\n"
            "  \"bits\" : \"xxxxxxxx\",              (string) compressed "
            "target of next block\n"
            "  \"height\" : n                      (numeric) The height of the "
            "next block\n"
            "}\n"

            "\nExamples:\n" +
            HelpExampleCli("getblocktemplate", "") +
            HelpExampleRpc("getblocktemplate", ""));
    }

    LOCK(cs_main);// 上锁

    std::string strMode = "template";// 模式，默认为 "template"
    UniValue lpval = NullUniValue;
    std::set<std::string> setClientRules;
    int64_t nMaxVersionPreVB = -1;
    if (request.params.size() > 0) {// 指定了参数
        const UniValue &oparam = request.params[0].get_obj();// 获取参数对象
        const UniValue &modeval = find_value(oparam, "mode");// 获取 "mode" 关键字对应的值
        if (modeval.isStr()) {// 字符串类型
            strMode = modeval.get_str();// 获取指定模式
        } else if (modeval.isNull()) {
            /* Do nothing */
        } else {// 其它类型
            throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");
        }
        lpval = find_value(oparam, "longpollid");

        if (strMode == "proposal") {// "proposal" 模式
            const UniValue &dataval = find_value(oparam, "data"); // 获取数据
            if (!dataval.isStr()) {
                throw JSONRPCError(RPC_TYPE_ERROR,
                                   "Missing data String key for proposal");
            }

            CBlock block;
            if (!DecodeHexBlk(block, dataval.get_str())) {// 解码 16 进制的区块
                throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                                   "Block decode failed");
            }

            uint256 hash = block.GetHash();// 获取区块哈希
            BlockMap::iterator mi = mapBlockIndex.find(hash);// 在区块索引列表中查找指定区块
            if (mi != mapBlockIndex.end()) {// 若找到
                CBlockIndex *pindex = mi->second;// 获取指定区块索引指针
                if (pindex->IsValid(BLOCK_VALID_SCRIPTS)) {// 验证区块
                    return "duplicate";
                }
                if (pindex->nStatus & BLOCK_FAILED_MASK) {// 区块状态
                    return "duplicate-invalid";
                }
                return "duplicate-inconclusive";
            }

            CBlockIndex *const pindexPrev = chainActive.Tip();// 获取激活链的tip
            // TestBlockValidity only supports blocks built on the current Tip
            if (block.hashPrevBlock != pindexPrev->GetBlockHash()) {// 指定区块的前一个区块哈希是否为当前链尖区块
                return "inconclusive-not-best-prevblk";
            }
            CValidationState state;
            TestBlockValidity(config, state, Params(), block, pindexPrev, false,
                              true);// 测试区块有效性
            return BIP22ValidationResult(config, state); // 返回验证结果
        }

        const UniValue &aClientRules = find_value(oparam, "rules");
        if (aClientRules.isArray()) {
            for (size_t i = 0; i < aClientRules.size(); ++i) {
                const UniValue &v = aClientRules[i];
                setClientRules.insert(v.get_str());
            }
        } else {
            // NOTE: It is important that this NOT be read if versionbits is
            // supported
            const UniValue &uvMaxVersion = find_value(oparam, "maxversion");
            if (uvMaxVersion.isNum()) {
                nMaxVersionPreVB = uvMaxVersion.get_int64();
            }
        }
    }

    if (strMode != "template") {// "template" 模式
        throw JSONRPCError(RPC_INVALID_PARAMETER, "Invalid mode");
    }

    if (!g_connman) {
        throw JSONRPCError(
            RPC_CLIENT_P2P_DISABLED,
            "Error: Peer-to-peer functionality missing or disabled");
    }

    if (g_connman->GetNodeCount(CConnman::CONNECTIONS_ALL) == 0) {// 已建立连接的节点列表非空
        throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED,
                           "Bitcoin is not connected!");
    }

    if (IsInitialBlockDownload()) {// 检查是否初始化块下载完成
        throw JSONRPCError(RPC_CLIENT_IN_INITIAL_DOWNLOAD,
                           "Bitcoin is downloading blocks...");
    }

    static unsigned int nTransactionsUpdatedLast;

    if (!lpval.isNull()) {
        // 等待响应，直到最佳块改变，或 1 分钟过去有更多的交易
        // Wait to respond until either the best block changes, OR a minute has
        // passed and there are more transactions
        uint256 hashWatchedChain;
        boost::system_time checktxtime;
        unsigned int nTransactionsUpdatedLastLP;

        if (lpval.isStr()) {
            // Format: <hashBestChain><nTransactionsUpdatedLast>
            std::string lpstr = lpval.get_str();

            hashWatchedChain.SetHex(lpstr.substr(0, 64));
            nTransactionsUpdatedLastLP = atoi64(lpstr.substr(64));
        } else {
            //规范没有对非字符串的 longpollip 指定行为，但这使测试更加容易
            // NOTE: Spec does not specify behaviour for non-string longpollid,
            // but this makes testing easier
            hashWatchedChain = chainActive.Tip()->GetBlockHash();// 获取链尖区块哈希
            nTransactionsUpdatedLastLP = nTransactionsUpdatedLast;// 最新的交易更新数量
        }

        // Release the wallet and main lock while waiting
        LEAVE_CRITICAL_SECTION(cs_main);// 在等待时释放钱包和主锁
        {
            checktxtime =
                boost::get_system_time() + boost::posix_time::minutes(1);// 检查交易时间为 1 分钟后

            boost::unique_lock<boost::mutex> lock(csBestBlock); // 最佳区块上锁
            while (chainActive.Tip()->GetBlockHash() == hashWatchedChain &&
                   IsRPCRunning()) {// 最佳区块未改变 且 RPC 服务开启
                if (!cvBlockChange.timed_wait(lock, checktxtime)) {// 超时：检查交易用于更新
                    // Timeout: Check transactions for update
                    if (mempool.GetTransactionsUpdated() !=
                        nTransactionsUpdatedLastLP) {
                        break;
                    }
                    checktxtime += boost::posix_time::seconds(10);// 检查时间加 10 秒
                }
            }
        }
        ENTER_CRITICAL_SECTION(cs_main);

        if (!IsRPCRunning()) {// 检查 RPC 服务是否开启
            throw JSONRPCError(RPC_CLIENT_NOT_CONNECTED, "Shutting down");
        }
        // TODO: Maybe recheck connections/IBD and (if something wrong) send an
        // expires-immediately template to stop miners?
    }

    // Update block// 更新区块
    static CBlockIndex *pindexPrev;
    static int64_t nStart;
    static std::unique_ptr<CBlockTemplate> pblocktemplate;
    if (pindexPrev != chainActive.Tip() ||// 最佳区块非空 或
        (mempool.GetTransactionsUpdated() != nTransactionsUpdatedLast &&
         GetTime() - nStart > 5)) {// 交易内存池交易更新数量不等于最近交易更新数 且 当前时间过去 5 秒
        // Clear pindexPrev so future calls make a new block, despite any
        // failures from here on
        // 清空 pindexPrev 以便将来调用创建一个新块，尽管这里可能会失败
        pindexPrev = nullptr;// 置空

        // Store the pindexBest used before CreateNewBlock, to avoid races
        nTransactionsUpdatedLast = mempool.GetTransactionsUpdated();// 获取当前交易更新数
        CBlockIndex *pindexPrevNew = chainActive.Tip();// 获取链尖索引
        nStart = GetTime();

        // Create new block
        CScript scriptDummy = CScript() << OP_TRUE;// 脚本
        pblocktemplate =
            BlockAssembler(config, Params()).CreateNewBlock(scriptDummy);// 创建一个新块
        if (!pblocktemplate) {
            throw JSONRPCError(RPC_OUT_OF_MEMORY, "Out of memory");
        }

        // Need to update only after we know CreateNewBlock succeeded
        pindexPrev = pindexPrevNew;// 在我们直到创建新块成功后需要更新前一个区块的哈希
    }
    CBlock *pblock = &pblocktemplate->block; // pointer for convenience
    const Consensus::Params &consensusParams = Params().GetConsensus();

    // Update nTime
    UpdateTime(pblock, consensusParams, pindexPrev);// 更新时间
    pblock->nNonce = 0;// 初始化随机数

    UniValue aCaps(UniValue::VARR);
    aCaps.push_back("proposal");

    UniValue transactions(UniValue::VARR);
    std::map<uint256, int64_t> setTxIndex;// 交易索引映射列表
    int i = 0;
    for (const auto &it : pblock->vtx) {// 遍历区块交易索引列表
        const CTransaction &tx = *it;
        uint256 txId = tx.GetId();// 获取交易哈希
        setTxIndex[txId] = i++;// 加入交易索引映射列表

        if (tx.IsCoinBase()) {// 若为创币交易
            continue;// 跳过
        }

        UniValue entry(UniValue::VOBJ);

        entry.push_back(Pair("data", EncodeHexTx(tx)));// 编码 16 进制的交易
        entry.push_back(Pair("txid", txId.GetHex()));
        entry.push_back(Pair("hash", tx.GetHash().GetHex()));// 获取 16 进制的交易索引

        UniValue deps(UniValue::VARR);
        for (const CTxIn &in : tx.vin) {// 遍历交易输入列表
            if (setTxIndex.count(in.prevout.hash))// 若前一笔交易输出在交易索引映射列表中
                deps.push_back(setTxIndex[in.prevout.hash]);// 加入依赖 json 数组
        }
        entry.push_back(Pair("depends", deps));// 依赖交易

        int index_in_template = i - 1;// 当前交易的索引序号
        entry.push_back(Pair(
            "fee", pblocktemplate->vTxFees[index_in_template].GetSatoshis()));// 交易费
        int64_t nTxSigOps = pblocktemplate->vTxSigOpsCount[index_in_template];// 交易签名操作 //？todo：
        entry.push_back(Pair("sigops", nTxSigOps));

        transactions.push_back(entry);
    }

    UniValue aux(UniValue::VOBJ);
    aux.push_back(
        Pair("flags", HexStr(COINBASE_FLAGS.begin(), COINBASE_FLAGS.end())));

    arith_uint256 hashTarget = arith_uint256().SetCompact(pblock->nBits);// 计算难度目标值

    UniValue aMutable(UniValue::VARR);
    aMutable.push_back("time");// 时间
    aMutable.push_back("transactions");//交易
    aMutable.push_back("prevblock");//前一个区块

    UniValue result(UniValue::VOBJ);
    result.push_back(Pair("capabilities", aCaps));

    UniValue aRules(UniValue::VARR);
    UniValue vbavailable(UniValue::VOBJ);
    for (int j = 0; j < (int)Consensus::MAX_VERSION_BITS_DEPLOYMENTS; ++j) {
        Consensus::DeploymentPos pos = Consensus::DeploymentPos(j);
        ThresholdState state = VersionBitsState(pindexPrev, consensusParams,
                                                pos, versionbitscache);
        switch (state) {
            case THRESHOLD_DEFINED:
            case THRESHOLD_FAILED:
                // Not exposed to GBT at all
                break;
            case THRESHOLD_LOCKED_IN:
                // Ensure bit is set in block version
                pblock->nVersion |= VersionBitsMask(consensusParams, pos);

            // FALLTHROUGH to get vbavailable set...
            case THRESHOLD_STARTED: {
                const struct BIP9DeploymentInfo &vbinfo =
                    VersionBitsDeploymentInfo[pos];
                vbavailable.push_back(Pair(
                    gbt_vb_name(pos), consensusParams.vDeployments[pos].bit));
                if (setClientRules.find(vbinfo.name) == setClientRules.end()) {
                    if (!vbinfo.gbt_force) {
                        // If the client doesn't support this, don't indicate it
                        // in the [default] version
                        pblock->nVersion &=
                            ~VersionBitsMask(consensusParams, pos);
                    }
                }
                break;
            }
            case THRESHOLD_ACTIVE: {
                // Add to rules only
                const struct BIP9DeploymentInfo &vbinfo =
                    VersionBitsDeploymentInfo[pos];
                aRules.push_back(gbt_vb_name(pos));
                if (setClientRules.find(vbinfo.name) == setClientRules.end()) {
                    // Not supported by the client; make sure it's safe to
                    // proceed
                    if (!vbinfo.gbt_force) {
                        // If we do anything other than throw an exception here,
                        // be sure version/force isn't sent to old clients
                        throw JSONRPCError(
                            RPC_INVALID_PARAMETER,
                            strprintf("Support for '%s' rule requires explicit "
                                      "client support",
                                      vbinfo.name));
                    }
                }
                break;
            }
        }
    }
    result.push_back(Pair("version", pblock->nVersion));// 区块版本
    result.push_back(Pair("rules", aRules));
    result.push_back(Pair("vbavailable", vbavailable));
    result.push_back(Pair("vbrequired", int(0)));

    if (nMaxVersionPreVB >= 2) {
        // If VB is supported by the client, nMaxVersionPreVB is -1, so we won't
        // get here. Because BIP 34 changed how the generation transaction is
        // serialized, we can only use version/force back to v2 blocks. This is
        // safe to do [otherwise-]unconditionally only because we are throwing
        // an exception above if a non-force deployment gets activated. Note
        // that this can probably also be removed entirely after the first BIP9
        // non-force deployment (ie, probably segwit) gets activated.
        aMutable.push_back("version/force");
    }

    result.push_back(Pair("previousblockhash", pblock->hashPrevBlock.GetHex()));//前一个区块hash
    result.push_back(Pair("trxansactions", transactions));//交易
    result.push_back(Pair("coinbaseaux", aux));
    result.push_back(
        Pair("coinbasevalue",
             (int64_t)pblock->vtx[0]->vout[0].nValue.GetSatoshis()));//coinbase输出的金额
    result.push_back(
        Pair("longpollid", chainActive.Tip()->GetBlockHash().GetHex() +
                               i64tostr(nTransactionsUpdatedLast)));
    result.push_back(Pair("target", hashTarget.GetHex()));//难度目标
    result.push_back(
        Pair("mintime", (int64_t)pindexPrev->GetMedianTimePast() + 1));
    result.push_back(Pair("mutable", aMutable));
    result.push_back(Pair("noncerange", "00000000ffffffff"));//随机数范围
    // FIXME: Allow for mining block greater than 1M.  允许挖出大于1M的块
    result.push_back(
        Pair("sigoplimit", GetMaxBlockSigOpsCount(DEFAULT_MAX_BLOCK_SIZE)));//区块签名操作
    result.push_back(Pair("sizelimit", DEFAULT_MAX_BLOCK_SIZE));//区块大小上限
    result.push_back(Pair("curtime", pblock->GetBlockTime()));//创建区块时间
    result.push_back(Pair("bits", strprintf("%08x", pblock->nBits)));//难度
    result.push_back(Pair("height", (int64_t)(pindexPrev->nHeight + 1)));//高度

    return result;
}

class submitblock_StateCatcher : public CValidationInterface {
public:
    uint256 hash;
    bool found;
    CValidationState state;

    submitblock_StateCatcher(const uint256 &hashIn)
        : hash(hashIn), found(false), state() {}

protected:
    virtual void BlockChecked(const CBlock &block,
                              const CValidationState &stateIn) {
        if (block.GetHash() != hash) {
            return;
        }

        found = true;
        state = stateIn;
    }
};
//基本流程：
//1.处理命令帮助和参数个数。
//2.解码 16 进制的区块数据。
//3.获取区块哈希。
//4.查找该区块是否存在，若存在，…
//5.若不存在，…
static UniValue submitblock(const Config &config,
                            const JSONRPCRequest &request) {

    // 参数只有 1 个
    if (request.fHelp || request.params.size() < 1 ||
        request.params.size() > 2) {
        // 命令帮助反馈
        throw std::runtime_error(
            "submitblock \"hexdata\" ( \"jsonparametersobject\" )\n"
            "\nAttempts to submit new block to network.\n"
            "The 'jsonparametersobject' parameter is currently ignored.\n"
            "See https://en.bitcoin.it/wiki/BIP_0022 for full specification.\n"

            "\nArguments\n"
            "1. \"hexdata\"        (string, required) the hex-encoded block "
            "data to submit\n"
            "2. \"parameters\"     (string, optional) object of optional "
            "parameters\n"
            "    {\n"
            "      \"workid\" : \"id\"    (string, optional) if the server "
            "provided a workid, it MUST be included with submissions\n"
            "    }\n"
            "\nResult:\n"
            "\nExamples:\n" +
            HelpExampleCli("submitblock", "\"mydata\"") +
            HelpExampleRpc("submitblock", "\"mydata\""));
    }

    std::shared_ptr<CBlock> blockptr = std::make_shared<CBlock>();
    CBlock &block = *blockptr;
    // 解码 16 进制的区块数据
    if (!DecodeHexBlk(block, request.params[0].get_str())) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR, "Block decode failed");
    }

    if (block.vtx.empty() || !block.vtx[0]->IsCoinBase()) {
        throw JSONRPCError(RPC_DESERIALIZATION_ERROR,
                           "Block does not start with a coinbase");
    }

    // 获取区块哈希
    uint256 hash = block.GetHash();
    bool fBlockPresent = false;
    {
        LOCK(cs_main);
        // 通过区块索引得到该区块对应迭代器
        BlockMap::iterator mi = mapBlockIndex.find(hash);
        if (mi != mapBlockIndex.end()) {// 如果找到了
            CBlockIndex *pindex = mi->second;// 获取其区块索引
            if (pindex->IsValid(BLOCK_VALID_SCRIPTS)) {
                return "duplicate";
            }
            if (pindex->nStatus & BLOCK_FAILED_MASK) {
                return "duplicate-invalid";
            }
            // Otherwise, we might only have the header - process the block
            // before returning
            fBlockPresent = true;
        }
    }

    submitblock_StateCatcher sc(block.GetHash());
    RegisterValidationInterface(&sc);
    bool fAccepted = ProcessNewBlock(config, blockptr, true, nullptr);
    UnregisterValidationInterface(&sc);
    if (fBlockPresent) {
        if (fAccepted && !sc.found) {
            return "duplicate-inconclusive";
        }
        return "duplicate";
    }

    if (!sc.found) {
        return "inconclusive";
    }

    return BIP22ValidationResult(config, sc.state);
}

//估算交易在 `nblocks` 个区块开始确认的每千字节的大致费用
//返回预估的每千字节的交易费。
//如果没有足够的交易和区块用来估算则会返回一个负值，-1 表示交易费为 0。

//基本流程：
//1.处理命令帮助和参数个数。
//2.参数类型检查。
//3.获取指定的块数，最低为 1 块。
//4.在交易内存池中通过块数预估交易费。
//5.若预估交易费为 0，则返回 -1。
//6.否则获取每千字节的交易费并返回。
static UniValue estimatefee(const Config &config,
                            const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() != 1) {// 参数必须为 1 个
        throw std::runtime_error(
            "estimatefee nblocks\n"
            "\nEstimates the approximate fee per kilobyte needed for a "
            "transaction to begin\n"
            "confirmation within nblocks blocks.\n"
            "\nArguments:\n"
            "1. nblocks     (numeric, required)\n"
            "\nResult:\n"
            "n              (numeric) estimated fee-per-kilobyte\n"
            "\n"
            "A negative value is returned if not enough transactions and "
            "blocks\n"
            "have been observed to make an estimate.\n"
            "-1 is always returned for nblocks == 1 as it is impossible to "
            "calculate\n"
            "a fee that is high enough to get reliably included in the next "
            "block.\n"
            "\nExample:\n" +
            HelpExampleCli("estimatefee", "6"));
    }

    RPCTypeCheck(request.params, {UniValue::VNUM});// 参数类型检查

    int nBlocks = request.params[0].get_int();// 获取指定的块数
    if (nBlocks < 1) {// 块数最低为 1
        nBlocks = 1;
    }

    CFeeRate feeRate = mempool.estimateFee(nBlocks);// 交易内存池预估交易费（根据区块数）
    if (feeRate == CFeeRate(0)) {// 若交易费为 0
        return -1.0;
    }

    return ValueFromAmount(feeRate.GetFeePerK());
}

static UniValue estimatepriority(const Config &config,
                                 const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() != 1) {
        throw std::runtime_error(
            "estimatepriority nblocks\n"
            "\nDEPRECATED. Estimates the approximate priority "
            "a zero-fee transaction needs to begin\n"
            "confirmation within nblocks blocks.\n"
            "\nArguments:\n"
            "1. nblocks     (numeric, required)\n"
            "\nResult:\n"
            "n              (numeric) estimated priority\n"
            "\n"
            "A negative value is returned if not enough "
            "transactions and blocks\n"
            "have been observed to make an estimate.\n"
            "\nExample:\n" +
            HelpExampleCli("estimatepriority", "6"));
    }

    RPCTypeCheck(request.params, {UniValue::VNUM});

    int nBlocks = request.params[0].get_int();
    if (nBlocks < 1) {
        nBlocks = 1;
    }

    return mempool.estimatePriority(nBlocks);
}

static UniValue estimatesmartfee(const Config &config,
                                 const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() != 1) {
        throw std::runtime_error(
            "estimatesmartfee nblocks\n"
            "\nWARNING: This interface is unstable and may disappear or "
            "change!\n"
            "\nEstimates the approximate fee per kilobyte needed for a "
            "transaction to begin\n"
            "confirmation within nblocks blocks if possible and return the "
            "number of blocks\n"
            "for which the estimate is valid.\n"
            "\nArguments:\n"
            "1. nblocks     (numeric)\n"
            "\nResult:\n"
            "{\n"
            "  \"feerate\" : x.x,     (numeric) estimate fee-per-kilobyte (in "
            "BCC)\n"
            "  \"blocks\" : n         (numeric) block number where estimate "
            "was found\n"
            "}\n"
            "\n"
            "A negative value is returned if not enough transactions and "
            "blocks\n"
            "have been observed to make an estimate for any number of blocks.\n"
            "However it will not return a value below the mempool reject fee.\n"
            "\nExample:\n" +
            HelpExampleCli("estimatesmartfee", "6"));
    }

    RPCTypeCheck(request.params, {UniValue::VNUM});

    int nBlocks = request.params[0].get_int();

    UniValue result(UniValue::VOBJ);
    int answerFound;
    CFeeRate feeRate = mempool.estimateSmartFee(nBlocks, &answerFound);
    result.push_back(Pair(
        "feerate",
        feeRate == CFeeRate(0) ? -1.0 : ValueFromAmount(feeRate.GetFeePerK())));
    result.push_back(Pair("blocks", answerFound));
    return result;
}

static UniValue estimatesmartpriority(const Config &config,
                                      const JSONRPCRequest &request) {
    if (request.fHelp || request.params.size() != 1) {
        throw std::runtime_error(
            "estimatesmartpriority nblocks\n"
            "\nDEPRECATED. WARNING: This interface is unstable and may "
            "disappear or change!\n"
            "\nEstimates the approximate priority a zero-fee transaction needs "
            "to begin\n"
            "confirmation within nblocks blocks if possible and return the "
            "number of blocks\n"
            "for which the estimate is valid.\n"
            "\nArguments:\n"
            "1. nblocks     (numeric, required)\n"
            "\nResult:\n"
            "{\n"
            "  \"priority\" : x.x,    (numeric) estimated priority\n"
            "  \"blocks\" : n         (numeric) block number where estimate "
            "was found\n"
            "}\n"
            "\n"
            "A negative value is returned if not enough transactions and "
            "blocks\n"
            "have been observed to make an estimate for any number of blocks.\n"
            "However if the mempool reject fee is set it will return 1e9 * "
            "MAX_MONEY.\n"
            "\nExample:\n" +
            HelpExampleCli("estimatesmartpriority", "6"));
    }

    RPCTypeCheck(request.params, {UniValue::VNUM});

    int nBlocks = request.params[0].get_int();

    UniValue result(UniValue::VOBJ);
    int answerFound;
    double priority = mempool.estimateSmartPriority(nBlocks, &answerFound);
    result.push_back(Pair("priority", priority));
    result.push_back(Pair("blocks", answerFound));
    return result;
}

// clang-format off
static const CRPCCommand commands[] = {
    //  category   name                     actor (function)       okSafeMode
    //  ---------- ------------------------ ---------------------- ----------
    {"mining",     "getnetworkhashps",      getnetworkhashps,      true, {"nblocks", "height"}},
    {"mining",     "getmininginfo",         getmininginfo,         true, {}},
    {"mining",     "prioritisetransaction", prioritisetransaction, true, {"txid", "priority_delta", "fee_delta"}},
    {"mining",     "getblocktemplate",      getblocktemplate,      true, {"template_request"}},
    {"mining",     "submitblock",           submitblock,           true, {"hexdata", "parameters"}},

    {"generating", "generate",              generate,              true, {"nblocks", "maxtries"}},
    {"generating", "generatetoaddress",     generatetoaddress,     true, {"nblocks", "address", "maxtries"}},

    {"util",       "estimatefee",           estimatefee,           true, {"nblocks"}},
    {"util",       "estimatepriority",      estimatepriority,      true, {"nblocks"}},
    {"util",       "estimatesmartfee",      estimatesmartfee,      true, {"nblocks"}},
    {"util",       "estimatesmartpriority", estimatesmartpriority, true, {"nblocks"}},
};
// clang-format on

void RegisterMiningRPCCommands(CRPCTable &t) {
    for (unsigned int vcidx = 0; vcidx < ARRAYLEN(commands); vcidx++)
        t.appendCommand(commands[vcidx].name, &commands[vcidx]);
}
