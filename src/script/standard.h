// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_SCRIPT_STANDARD_H
#define BITCOIN_SCRIPT_STANDARD_H

#include "script/interpreter.h"
#include "uint256.h"

#include <boost/variant.hpp>

#include <cstdint>

static const bool DEFAULT_ACCEPT_DATACARRIER = true;

class CKeyID;
class CScript;

/** A reference to a CScript: the Hash160 of its serialization (see script.h) */
class CScriptID : public uint160 {
public:
    CScriptID() : uint160() {}
    CScriptID(const CScript &in);
    CScriptID(const uint160 &in) : uint160(in) {}
};

//!< bytes (+1 for OP_RETURN, +2 for the pushdata opcodes)
static const unsigned int MAX_OP_RETURN_RELAY = 83;
extern bool fAcceptDatacarrier;
extern unsigned nMaxDatacarrierBytes;

/**
 * Mandatory script verification flags that all new blocks must comply with for
 * them to be valid. (but old blocks may not comply with) Currently just P2SH,
 * but in the future other flags may be added, such as a soft-fork to enforce
 * strict DER encoding.
 *
 * Failing one of these tests may trigger a DoS ban - see CheckInputs() for
 * details.
 * 强制性脚本验证标识，所有的新区块必须使用该标志验证 为有效。(因为以前有的区块并没有全部采用该验证标识)；
 * 当前主要是P2SH标识(该标识是后来添加的)；但是在未来可能还有其他的验证标志被添加，例如软分叉强制执行严格
 * 的DER编码。
 * 如果这些测试中的任何一个失败，都可能触发DOS禁令。细节看CheckInputs
 */
static const unsigned int MANDATORY_SCRIPT_VERIFY_FLAGS =
    SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_STRICTENC | SCRIPT_ENABLE_SIGHASH_FORKID;

enum txnouttype {
    TX_NONSTANDARD,     //非标准交易
    // 'standard' transaction types:
    TX_PUBKEY,          //花费到公钥的标准交易          p2pk
    TX_PUBKEYHASH,      //花费到公钥哈希的标准交易       p2pkh
    TX_SCRIPTHASH,      //花费到脚本哈希的标准交易      p2sh
    TX_MULTISIG,        //多重签名的交易               交易输出中含有组合锁定脚本x-of-3的脚本
    TX_NULL_DATA,       //不可花费的交易
};

class CNoDestination {
public:
    friend bool operator==(const CNoDestination &a, const CNoDestination &b) {
        return true;
    }
    friend bool operator<(const CNoDestination &a, const CNoDestination &b) {
        return true;
    }
};

/**
 * A txout script template with a specific destination. It is either:
 *  * CNoDestination: no destination set
 *  * CKeyID: TX_PUBKEYHASH destination
 *  * CScriptID: TX_SCRIPTHASH destination
 *  A CTxDestination is the internal data type encoded in a bitcoin address
 */
typedef boost::variant<CNoDestination, CKeyID, CScriptID> CTxDestination;

const char *GetTxnOutputType(txnouttype t);
bool IsValidDestination(const CTxDestination &dest);

bool Solver(const CScript &scriptPubKey, txnouttype &typeRet,
            std::vector<std::vector<uint8_t>> &vSolutionsRet);
bool ExtractDestination(const CScript &scriptPubKey,
                        CTxDestination &addressRet);
bool ExtractDestinations(const CScript &scriptPubKey, txnouttype &typeRet,
                         std::vector<CTxDestination> &addressRet,
                         int &nRequiredRet);

CScript GetScriptForDestination(const CTxDestination &dest);
CScript GetScriptForRawPubKey(const CPubKey &pubkey);
CScript GetScriptForMultisig(int nRequired, const std::vector<CPubKey> &keys);

#endif // BITCOIN_SCRIPT_STANDARD_H
