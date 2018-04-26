// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "script/standard.h"

#include "pubkey.h"
#include "script/script.h"
#include "util.h"
#include "utilstrencodings.h"

typedef std::vector<uint8_t> valtype;

bool fAcceptDatacarrier = DEFAULT_ACCEPT_DATACARRIER;
unsigned nMaxDatacarrierBytes = MAX_OP_RETURN_RELAY;

CScriptID::CScriptID(const CScript &in)
    : uint160(Hash160(in.begin(), in.end())) {}

const char *GetTxnOutputType(txnouttype t) {
    switch (t) {
        case TX_NONSTANDARD:
            return "nonstandard";
        case TX_PUBKEY:
            return "pubkey";
        case TX_PUBKEYHASH:
            return "pubkeyhash";
        case TX_SCRIPTHASH:
            return "scripthash";
        case TX_MULTISIG:
            return "multisig";
        case TX_NULL_DATA:
            return "nulldata";
    }
    return nullptr;
}

/**
 * Return public keys or hashes from scriptPubKey, for 'standard' transaction
 * types. 对于标准的交易类型，从锁定脚本中返回公钥或哈希。
 */
bool Solver(const CScript &scriptPubKey, txnouttype &typeRet,
            std::vector<std::vector<uint8_t>> &vSolutionsRet) {
    //1. 生成模板； Templates
    static std::multimap<txnouttype, CScript> mTemplates;
    if (mTemplates.empty()) {
        // Standard tx, sender provides pubkey, receiver adds signature
        mTemplates.insert(
            std::make_pair(TX_PUBKEY, CScript() << OP_PUBKEY << OP_CHECKSIG));

        // Bitcoin address tx, sender provides hash of pubkey, receiver provides
        // signature and pubkey
        mTemplates.insert(std::make_pair(
            TX_PUBKEYHASH, CScript() << OP_DUP << OP_HASH160 << OP_PUBKEYHASH
                                     << OP_EQUALVERIFY << OP_CHECKSIG));

        // Sender provides N pubkeys, receivers provides M signatures
        mTemplates.insert(std::make_pair(
            TX_MULTISIG, CScript() << OP_SMALLINTEGER << OP_PUBKEYS
                                   << OP_SMALLINTEGER << OP_CHECKMULTISIG));
    }
    //2. 情况返回数据
    vSolutionsRet.clear();

    // Shortcut for pay-to-script-hash, which are more constrained than the
    // other types:
    // it is always OP_HASH160 20 [20 byte hash] OP_EQUAL
    //3. 判断该脚本是否 p2sh 脚本，如果是，赋值给传出变量，返回true。
    if (scriptPubKey.IsPayToScriptHash()) {
        typeRet = TX_SCRIPTHASH;
        std::vector<uint8_t> hashBytes(scriptPubKey.begin() + 2,
                                       scriptPubKey.begin() + 22);
        vSolutionsRet.push_back(hashBytes);
        return true;
    }

    // Provably prunable, data-carrying output
    //
    // So long as script passes the IsUnspendable() test and all but the first
    // byte passes the IsPushOnly() test we don't care what exactly is in the
    // script.
    //2. 判断脚本是否为 OP_RETURN 类型的脚本；如果是，赋值给传出变量，返回true。
    if (scriptPubKey.size() >= 1 && scriptPubKey[0] == OP_RETURN &&
        scriptPubKey.IsPushOnly(scriptPubKey.begin() + 1)) {
        typeRet = TX_NULL_DATA;
        return true;
    }

    // Scan templates
    //3. 扫描模板；
    const CScript &script1 = scriptPubKey;
    for (const std::pair<txnouttype, CScript> &tplate : mTemplates) {
        //4. 获取模板脚本，并清空传出脚本
        const CScript &script2 = tplate.second;
        vSolutionsRet.clear();

        opcodetype opcode1, opcode2;
        std::vector<uint8_t> vch1, vch2;

        // Compare；
        // pc1 : 输出脚本的起始位置
        CScript::const_iterator pc1 = script1.begin();
        // pc2 : 模板脚本的起始位置
        CScript::const_iterator pc2 = script2.begin();
        // 死循环，处理该脚本
        while (true) {
            //5. 如果两个迭代器都达到尾部，赋值给传出参数，然后退出。
            if (pc1 == script1.end() && pc2 == script2.end()) {
                // Found a match
                typeRet = tplate.first;
                //当为 TX_MULTISIG 类型脚本时，需要判断签名与公钥个数是否正确，不正确，直接报错。
                if (typeRet == TX_MULTISIG) {
                    // Additional checks for TX_MULTISIG:
                    uint8_t m = vSolutionsRet.front()[0];
                    uint8_t n = vSolutionsRet.back()[0];
                    if (m < 1 || n < 1 || m > n ||
                        vSolutionsRet.size() - 2 != n)
                        return false;
                }
                return true;
            }
            // 获取脚本的操作码，以及操作码操作的内容
            if (!script1.GetOp(pc1, opcode1, vch1)) break;
            if (!script2.GetOp(pc2, opcode2, vch2)) break;

            // Template matching opcodes: 如果模板的操作码为 OP_PUBKEYS;
            // 这种情况是在交易输出脚本为 TX_MULTISIG 时出现。
            if (opcode2 == OP_PUBKEYS) {
                //当输出脚本的操作码 >=33 且 <=65 (压缩公钥与未压缩公钥)
                while (vch1.size() >= 33 && vch1.size() <= 65) {
                    // 将该公钥写入返回值中
                    vSolutionsRet.push_back(vch1);
                    // 继续移动迭代器，取下一个操作码
                    if (!script1.GetOp(pc1, opcode1, vch1)) break;
                }
                // 继续移动下一个操作码，取下一个操作码
                if (!script2.GetOp(pc2, opcode2, vch2)) break;
                // Normal situation is to fall through to other if/else
                // statements
            }

            //如果为
            if (opcode2 == OP_PUBKEY) {
                if (vch1.size() < 33 || vch1.size() > 65) break;
                vSolutionsRet.push_back(vch1);
            } else if (opcode2 == OP_PUBKEYHASH) {
                if (vch1.size() != sizeof(uint160)) break;
                vSolutionsRet.push_back(vch1);
            } else if (opcode2 == OP_SMALLINTEGER) {
                // Single-byte small integer pushed onto vSolutions
                if (opcode1 == OP_0 || (opcode1 >= OP_1 && opcode1 <= OP_16)) {
                    char n = (char)CScript::DecodeOP_N(opcode1);
                    vSolutionsRet.push_back(valtype(1, n));
                } else
                    break;
            } else if (opcode1 != opcode2 || vch1 != vch2) {
                // Others must match exactly
                break;
            }
        }
    }

    vSolutionsRet.clear();
    typeRet = TX_NONSTANDARD;
    return false;
}

bool ExtractDestination(const CScript &scriptPubKey,
                        CTxDestination &addressRet) {
    std::vector<valtype> vSolutions;
    txnouttype whichType;
    if (!Solver(scriptPubKey, whichType, vSolutions)) return false;

    if (whichType == TX_PUBKEY) {
        CPubKey pubKey(vSolutions[0]);
        if (!pubKey.IsValid()) return false;

        addressRet = pubKey.GetID();
        return true;
    } else if (whichType == TX_PUBKEYHASH) {
        addressRet = CKeyID(uint160(vSolutions[0]));
        return true;
    } else if (whichType == TX_SCRIPTHASH) {
        addressRet = CScriptID(uint160(vSolutions[0]));
        return true;
    }
    // Multisig txns have more than one address...
    return false;
}

bool ExtractDestinations(const CScript &scriptPubKey, txnouttype &typeRet,
                         std::vector<CTxDestination> &addressRet,
                         int &nRequiredRet) {
    addressRet.clear();
    typeRet = TX_NONSTANDARD;
    std::vector<valtype> vSolutions;
    if (!Solver(scriptPubKey, typeRet, vSolutions)) return false;
    if (typeRet == TX_NULL_DATA) {
        // This is data, not addresses
        return false;
    }

    if (typeRet == TX_MULTISIG) {
        nRequiredRet = vSolutions.front()[0];
        for (unsigned int i = 1; i < vSolutions.size() - 1; i++) {
            CPubKey pubKey(vSolutions[i]);
            if (!pubKey.IsValid()) continue;

            CTxDestination address = pubKey.GetID();
            addressRet.push_back(address);
        }

        if (addressRet.empty()) return false;
    } else {
        nRequiredRet = 1;
        CTxDestination address;
        if (!ExtractDestination(scriptPubKey, address)) return false;
        addressRet.push_back(address);
    }

    return true;
}

namespace {
class CScriptVisitor : public boost::static_visitor<bool> {
private:
    CScript *script;

public:
    CScriptVisitor(CScript *scriptin) { script = scriptin; }

    bool operator()(const CNoDestination &dest) const {
        script->clear();
        return false;
    }

    bool operator()(const CKeyID &keyID) const {
        script->clear();
        *script << OP_DUP << OP_HASH160 << ToByteVector(keyID) << OP_EQUALVERIFY
                << OP_CHECKSIG;
        return true;
    }

    bool operator()(const CScriptID &scriptID) const {
        script->clear();
        *script << OP_HASH160 << ToByteVector(scriptID) << OP_EQUAL;
        return true;
    }
};
}

CScript GetScriptForDestination(const CTxDestination &dest) {
    CScript script;

    boost::apply_visitor(CScriptVisitor(&script), dest);
    return script;
}

CScript GetScriptForRawPubKey(const CPubKey &pubKey) {
    return CScript() << std::vector<uint8_t>(pubKey.begin(), pubKey.end())
                     << OP_CHECKSIG;
}

CScript GetScriptForMultisig(int nRequired, const std::vector<CPubKey> &keys) {
    CScript script;

    script << CScript::EncodeOP_N(nRequired);
    for (const CPubKey &key : keys)
        script << ToByteVector(key);
    script << CScript::EncodeOP_N(keys.size()) << OP_CHECKMULTISIG;
    return script;
}

bool IsValidDestination(const CTxDestination &dest) {
    return dest.which() != 0;
}
