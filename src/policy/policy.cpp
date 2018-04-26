// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

// NOTE: This file is intended to be customised by the end user, and includes
// only local node policy logic

#include "policy/policy.h"

#include "tinyformat.h"
#include "util.h"
#include "utilstrencodings.h"
#include "validation.h"

/**
 * Check transaction inputs to mitigate two potential denial-of-service attacks:
 *
 * 1. scriptSigs with extra data stuffed into them, not consumed by scriptPubKey
 * (or P2SH script)
 * 2. P2SH scripts with a crazy number of expensive CHECKSIG/CHECKMULTISIG
 * operations
 *
 * Why bother? To avoid denial-of-service attacks; an attacker can submit a
 * standard HASH... OP_EQUAL transaction, which will get accepted into blocks.
 * The redemption script can be anything; an attacker could use a very
 * expensive-to-check-upon-redemption script like:
 *   DUP CHECKSIG DROP ... repeated 100 times... OP_1
 */
// 检查一个交易的输出脚本 是否为标准交易类型的 脚本， 并返回 该脚本的类型。
// whichType(out): 该脚本类型
bool IsStandard(const CScript &scriptPubKey, txnouttype &whichType) {
    std::vector<std::vector<uint8_t>> vSolutions;
    //解析锁定脚本，并获取脚本类型以及该脚本的数据
    if (!Solver(scriptPubKey, whichType, vSolutions)) return false;

    //如果为 脚本输出为多签名的交易。
    if (whichType == TX_MULTISIG) {
        uint8_t m = vSolutions.front()[0];      // 获取签名的个数
        uint8_t n = vSolutions.back()[0];       // 获取公钥的个数
        // Support up to x-of-3 multisig txns as standard
        // 支持x-of-3的交易为标准交易。
        if (n < 1 || n > 3) return false;       //签名的数量应该 在1-3之间
        if (m < 1 || m > n) return false;       //公钥的数量应该小于签名的数量
    } else if (whichType == TX_NULL_DATA &&
               (!fAcceptDatacarrier ||
                scriptPubKey.size() > nMaxDatacarrierBytes))
        return false;

    return whichType != TX_NONSTANDARD;
}

bool IsStandardTx(const CTransaction &tx, std::string &reason, CTxOut &txout) {
    //1. 检查交易版本号
    if (tx.nVersion > CTransaction::MAX_STANDARD_VERSION || tx.nVersion < 1) {
        reason = "version";
        return false;
    }

    // Extremely large transactions with lots of inputs can cost the network
    // almost as much to process as they cost the sender in fees, because
    // computing signature hashes is O(ninputs*txsize). Limiting transactions
    // to MAX_STANDARD_TX_SIZE mitigates CPU exhaustion attacks.
    //2. 检查当前交易字节 是处于标准字节限制，大于，出错。
    unsigned int sz = GetTransactionSize(tx);
    if (sz >= MAX_STANDARD_TX_SIZE) {
        reason = "tx-size";
        return false;
    }

    //3. 检查所有的交易输入的签名字段，和签名脚本的操作码(签名脚本中，操作码只允许为push操作)
    for (const CTxIn &txin : tx.vin) {
        // Biggest 'standard' txin is a 15-of-15 P2SH multisig with compressed
        // keys (remember the 520 byte limit on redeemScript size). That works
        // out to a (15*(33+1))+3=513 byte redeemScript, 513+1+15*(73+1)+3=1627
        // bytes of scriptSig, which we round off to 1650 bytes for some minor
        // future-proofing. That's also enough to spend a 20-of-20 CHECKMULTISIG
        // scriptPubKey, though such a scriptPubKey is not considered standard.
        if (txin.scriptSig.size() > 1650) {
            reason = "scriptsig-size";
            return false;
        }
        if (!txin.scriptSig.IsPushOnly()) {
            reason = "scriptsig-not-pushonly";
            return false;
        }
    }

    //4. 检查交易的输出
    unsigned int nDataOut = 0;
    txnouttype whichType;
    for (const CTxOut &txout : tx.vout) {
        // 检查他是否为标准的输出脚本
        if (!::IsStandard(txout.scriptPubKey, whichType)) {
            reason = "scriptpubkey";
            return false;
        }

        // 检查叫虐类型
        if (whichType == TX_NULL_DATA)
            nDataOut++;
        else if ((whichType == TX_MULTISIG) && (!fIsBareMultisigStd)) {
            reason = "bare-multisig";
            return false;
        } else if (txout.IsDust(dustRelayFee)) {
            //输出金额过小，该交易未灰尘交易。
            reason = "dust";
            return false;
        }
    }

    // only one OP_RETURN txout is permitted；
    //5. 每个交易只允许存在一个 OP_RETURN 操作码
    if (nDataOut > 1) {
        reason = "multi-op-return";
        return false;
    }

    return true;
}

//查看该交易的所有引用输出的锁定脚本是否为标准类型的脚本。如果是，返回true，否，返回false。
//tx(in):检查的交易；     mapInputs(in):该view存储要检查交易的所有引用输出对应的coin。
bool AreInputsStandard(const CTransaction &tx,
                       const CCoinsViewCache &mapInputs) {
    //1. 通常，coinbase交易的交易没有引用其他的交易。
    if (tx.IsCoinBase()) {
        // Coinbases don't use vin normally.
        return true;
    }

    //2. 遍历交易输入；
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        //1. 获取 引用输入对应的 锁定输出信息。
        const CTxOut &prev = mapInputs.GetOutputFor(tx.vin[i]);

        std::vector<std::vector<uint8_t>> vSolutions;
        txnouttype whichType;
        //2. get the scriptPubKey corresponding to this input: 获取交易输入对应的锁定脚本
        const CScript &prevScript = prev.scriptPubKey;
        //3. 解析脚本，出错直接返回false。
        if (!Solver(prevScript, whichType, vSolutions)) return false;

        if (whichType == TX_SCRIPTHASH) {
            std::vector<std::vector<uint8_t>> stack;
            // convert the scriptSig into a stack, so we can inspect the
            // redeemScript； 将签名转换到stack中，用来检查赎回脚本；用来验证赎回脚本
            if (!EvalScript(stack, tx.vin[i].scriptSig, SCRIPT_VERIFY_NONE,
                            BaseSignatureChecker()))
                return false;
            if (stack.empty()) return false;    //标识验证出错
            CScript subscript(stack.back().begin(), stack.back().end());
            if (subscript.GetSigOpCount(true) > MAX_P2SH_SIGOPS) {
                return false;
            }
        }
    }

    return true;
}

// 默认的指定费率
CFeeRate incrementalRelayFee = CFeeRate(DEFAULT_INCREMENTAL_RELAY_FEE);
CFeeRate dustRelayFee = CFeeRate(DUST_RELAY_TX_FEE);
unsigned int nBytesPerSigOp = DEFAULT_BYTES_PER_SIGOP;
