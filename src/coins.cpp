// Copyright (c) 2012-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "coins.h"

#include "consensus/consensus.h"
#include "memusage.h"
#include "random.h"

#include <cassert>

bool CCoinsView::GetCoin(const COutPoint &outpoint, Coin &coin) const {
    return false;
}
bool CCoinsView::HaveCoin(const COutPoint &outpoint) const {
    return false;
}
uint256 CCoinsView::GetBestBlock() const {
    return uint256();
}
bool CCoinsView::BatchWrite(CCoinsMap &mapCoins, const uint256 &hashBlock) {
    return false;
}
CCoinsViewCursor *CCoinsView::Cursor() const {
    return nullptr;
}

CCoinsViewBacked::CCoinsViewBacked(CCoinsView *viewIn) : base(viewIn) {}

bool CCoinsViewBacked::GetCoin(const COutPoint &outpoint, Coin &coin) const {
    return base->GetCoin(outpoint, coin);
}
bool CCoinsViewBacked::HaveCoin(const COutPoint &outpoint) const {
    return base->HaveCoin(outpoint);
}
uint256 CCoinsViewBacked::GetBestBlock() const {
    return base->GetBestBlock();
}
void CCoinsViewBacked::SetBackend(CCoinsView &viewIn) {
    base = &viewIn;
}
bool CCoinsViewBacked::BatchWrite(CCoinsMap &mapCoins,
                                  const uint256 &hashBlock) {
    return base->BatchWrite(mapCoins, hashBlock);
}
CCoinsViewCursor *CCoinsViewBacked::Cursor() const {
    return base->Cursor();
}
size_t CCoinsViewBacked::EstimateSize() const {
    return base->EstimateSize();
}

SaltedOutpointHasher::SaltedOutpointHasher()
    : k0(GetRand(std::numeric_limits<uint64_t>::max())),
      k1(GetRand(std::numeric_limits<uint64_t>::max())) {}

CCoinsViewCache::CCoinsViewCache(CCoinsView *baseIn)
    : CCoinsViewBacked(baseIn), cachedCoinsUsage(0) {}

size_t CCoinsViewCache::DynamicMemoryUsage() const {
    return memusage::DynamicUsage(cacheCoins) + cachedCoinsUsage;
}

// 在UTXO集中查找该 preOut。
// 1. 先在缓存中找，未找到时，2. 进入数据库查找，如果数据也未找到，直接返回缓存的结束迭代器；
// 如果找到，将它插入缓存中，并返回插入位置的迭代器。
CCoinsMap::iterator
CCoinsViewCache::FetchCoin(const COutPoint &outpoint) const {
    //1. 在缓存中找到，直接返回。
    CCoinsMap::iterator it = cacheCoins.find(outpoint);
    if (it != cacheCoins.end()) {
        return it;
    }
    //2. 去数据库中查找，未找到时，返回缓存的结束迭代器。
    Coin tmp;
    if (!base->GetCoin(outpoint, tmp)) {
        return cacheCoins.end();
    }
    //3. 在数据库中找到，将该UTXO写入缓存。
    CCoinsMap::iterator ret =
        cacheCoins
            .emplace(std::piecewise_construct, std::forward_as_tuple(outpoint),
                     std::forward_as_tuple(std::move(tmp)))
            .first;
    //4. 查看该交易是否已花费，TRUE已花费。
    if (ret->second.coin.IsSpent()) {
        // The parent only has an empty entry for this outpoint; we can consider
        // our version as fresh.
        ret->second.flags = CCoinsCacheEntry::FRESH;
    }
    //5. 更新内存的使用量
    cachedCoinsUsage += ret->second.coin.DynamicMemoryUsage();
    return ret;
}

bool CCoinsViewCache::GetCoin(const COutPoint &outpoint, Coin &coin) const {
    CCoinsMap::const_iterator it = FetchCoin(outpoint);
    if (it == cacheCoins.end()) {
        return false;
    }
    coin = it->second.coin;
    return true;
}

//向UTXO集合中添加coin；outpoint(in):该交易输出；coin(in):该交易输出对应的UTXO。
void CCoinsViewCache::AddCoin(const COutPoint &outpoint, Coin coin,
                              bool possible_overwrite) {
    assert(!coin.IsSpent());
    // 不可花费的交易不加入UTXO集合
    if (coin.GetTxOut().scriptPubKey.IsUnspendable()) {
        return;
    }
    CCoinsMap::iterator it;
    bool inserted;
    std::tie(it, inserted) =
        cacheCoins.emplace(std::piecewise_construct,
                           std::forward_as_tuple(outpoint), std::tuple<>());
    bool fresh = false;
    //插入失败
    if (!inserted) {
        cachedCoinsUsage -= it->second.coin.DynamicMemoryUsage();
    }
    //非coinbase交易。
    if (!possible_overwrite) {
        //添加的未裁剪条目的新币。 如果该币未花费
        if (!it->second.coin.IsSpent()) {
            throw std::logic_error(
                "Adding new coin that replaces non-pruned entry");
        }
        fresh = !(it->second.flags & CCoinsCacheEntry::DIRTY);
    }
    it->second.coin = std::move(coin);
    it->second.flags |=
        CCoinsCacheEntry::DIRTY | (fresh ? CCoinsCacheEntry::FRESH : 0);
    cachedCoinsUsage += it->second.coin.DynamicMemoryUsage();
}

//为当前交易的输出构造UTXO，然后插入UTXO集合中
void AddCoins(CCoinsViewCache &cache, const CTransaction &tx, int nHeight) {
    bool fCoinbase = tx.IsCoinBase();
    const uint256 &txid = tx.GetHash();
    for (size_t i = 0; i < tx.vout.size(); ++i) {
        // Pass fCoinbase as the possible_overwrite flag to AddCoin, in order to
        // correctly deal with the pre-BIP30 occurrances of duplicate coinbase
        // transactions.
        cache.AddCoin(COutPoint(txid, i), Coin(tx.vout[i], nHeight, fCoinbase),
                      fCoinbase);
    }
}

//outpoint(in):引用的交易输出；moveout(out):该引用输出在UTXO集合中的存储币
bool CCoinsViewCache::SpendCoin(const COutPoint &outpoint, Coin *moveout) {
    CCoinsMap::iterator it = FetchCoin(outpoint);
    if (it == cacheCoins.end()) {
        return false;
    }
    cachedCoinsUsage -= it->second.coin.DynamicMemoryUsage();
    if (moveout) {
        *moveout = std::move(it->second.coin);
    }
    if (it->second.flags & CCoinsCacheEntry::FRESH) {
        cacheCoins.erase(it);       //从缓存中删除该交易
    } else {
        it->second.flags |= CCoinsCacheEntry::DIRTY;
        it->second.coin.Clear();
    }
    return true;
}

static const Coin coinEmpty;

//获取outpoint对应的coin
const Coin &CCoinsViewCache::AccessCoin(const COutPoint &outpoint) const {
    //1. 在UTXO集合中获取preOut的UTXO；如果未找到，直接返回一个NULL对象。否则，返回一个有效的Coin
    CCoinsMap::const_iterator it = FetchCoin(outpoint);
    if (it == cacheCoins.end()) {
        return coinEmpty;
    }
    return it->second.coin;
}

//当存在该UTXO，并且该coin未花费，标识找到该UTXO，返回TRUE。
bool CCoinsViewCache::HaveCoin(const COutPoint &outpoint) const {
    CCoinsMap::const_iterator it = FetchCoin(outpoint);

    return it != cacheCoins.end() && !it->second.coin.IsSpent();
}

bool CCoinsViewCache::HaveCoinInCache(const COutPoint &outpoint) const {
    CCoinsMap::const_iterator it = cacheCoins.find(outpoint);
    return it != cacheCoins.end();
}

uint256 CCoinsViewCache::GetBestBlock() const {
    if (hashBlock.IsNull()) {
        hashBlock = base->GetBestBlock();
    }
    return hashBlock;
}

void CCoinsViewCache::SetBestBlock(const uint256 &hashBlockIn) {
    hashBlock = hashBlockIn;
}

//批量写UTXO集合在数据库
bool CCoinsViewCache::BatchWrite(CCoinsMap &mapCoins,
                                 const uint256 &hashBlockIn) {
    for (CCoinsMap::iterator it = mapCoins.begin(); it != mapCoins.end();) {
        // Ignore non-dirty entries (optimization). 忽略非脏的条目
        if (it->second.flags & CCoinsCacheEntry::DIRTY) {
            //在缓存中查找该UTXO是否存在
            CCoinsMap::iterator itUs = cacheCoins.find(it->first);
            //不存在，进入该条件。
            if (itUs == cacheCoins.end()) {
                // The parent cache does not have an entry, while the child does
                // We can ignore it if it's both FRESH and pruned in the child
                // 父缓存中没有这个条目，如果该条目的孩子同时处于FRESH 和 修改状态，同时可以忽略孩子。
                if (!(it->second.flags & CCoinsCacheEntry::FRESH &&
                      it->second.coin.IsSpent())) {
                    // Otherwise we will need to create it in the parent and
                    // move the data up and mark it as dirty
                    CCoinsCacheEntry &entry = cacheCoins[it->first];
                    entry.coin = std::move(it->second.coin);
                    cachedCoinsUsage += entry.coin.DynamicMemoryUsage();
                    entry.flags = CCoinsCacheEntry::DIRTY;
                    // We can mark it FRESH in the parent if it was FRESH in the
                    // child. Otherwise it might have just been flushed from the
                    // parent's cache and already exist in the grandparent
                    if (it->second.flags & CCoinsCacheEntry::FRESH)
                        entry.flags |= CCoinsCacheEntry::FRESH;
                }
            } else {
                // Assert that the child cache entry was not marked FRESH if the
                // parent cache entry has unspent outputs. If this ever happens,
                // it means the FRESH flag was misapplied and there is a logic
                // error in the calling code.
                if ((it->second.flags & CCoinsCacheEntry::FRESH) &&
                    !itUs->second.coin.IsSpent())
                    throw std::logic_error("FRESH flag misapplied to cache "
                                           "entry for base transaction with "
                                           "spendable outputs");

                // Found the entry in the parent cache
                if ((itUs->second.flags & CCoinsCacheEntry::FRESH) &&
                    it->second.coin.IsSpent()) {
                    // The grandparent does not have an entry, and the child is
                    // modified and being pruned. This means we can just delete
                    // it from the parent.
                    cachedCoinsUsage -= itUs->second.coin.DynamicMemoryUsage();
                    cacheCoins.erase(itUs);
                } else {
                    // A normal modification.
                    cachedCoinsUsage -= itUs->second.coin.DynamicMemoryUsage();
                    itUs->second.coin = std::move(it->second.coin);
                    cachedCoinsUsage += itUs->second.coin.DynamicMemoryUsage();
                    itUs->second.flags |= CCoinsCacheEntry::DIRTY;
                    // NOTE: It is possible the child has a FRESH flag here in
                    // the event the entry we found in the parent is pruned. But
                    // we must not copy that FRESH flag to the parent as that
                    // pruned state likely still needs to be communicated to the
                    // grandparent.
                }
            }
        }
        CCoinsMap::iterator itOld = it++;
        mapCoins.erase(itOld);
    }
    hashBlock = hashBlockIn;
    return true;
}

bool CCoinsViewCache::Flush() {
    bool fOk = base->BatchWrite(cacheCoins, hashBlock);
    cacheCoins.clear();
    cachedCoinsUsage = 0;
    return fOk;
}

void CCoinsViewCache::Uncache(const COutPoint &outpoint) {
    CCoinsMap::iterator it = cacheCoins.find(outpoint);
    if (it != cacheCoins.end() && it->second.flags == 0) {
        cachedCoinsUsage -= it->second.coin.DynamicMemoryUsage();
        cacheCoins.erase(it);
    }
}

unsigned int CCoinsViewCache::GetCacheSize() const {
    return cacheCoins.size();
}

const CTxOut &CCoinsViewCache::GetOutputFor(const CTxIn &input) const {
    //1.获取交易输入的引用输出对应的coin
    const Coin &coin = AccessCoin(input.prevout);
    //2. 该coin必须为未花费。
    assert(!coin.IsSpent());
    //3. 返回该coin对应的交易输出数据
    return coin.GetTxOut();
}

//返回一个交易所有交易输入在本节点的UTXO集合中的总金额。
Amount CCoinsViewCache::GetValueIn(const CTransaction &tx) const {
    //coinbase交易，直接返回0
    if (tx.IsCoinBase()) {
        return 0;
    }

    Amount nResult = 0;
    //遍历该交易的所有交易输入；从UTXO集合中查找所有这些交易输入的未花费总金额
    for (size_t i = 0; i < tx.vin.size(); i++) {
        nResult += GetOutputFor(tx.vin[i]).nValue;
    }

    return nResult;
}

// 遍历该交易的所有交易输入，查看它的所有交易输入的引用输出是否存在于本节点的UTXO集合中，只要有一个不存在，即返回false.
bool CCoinsViewCache::HaveInputs(const CTransaction &tx) const {
    //1. coinbase交易没有交易输入，所以直接返回TRUE。
    if (tx.IsCoinBase()) {
        return true;
    }

    //2. 遍历该交易的所有交易输入，查看它的所有交易输入的引用输出是否存在于本节点的UTXO集合中，只要有一个不存在，即返回false.
    for (size_t i = 0; i < tx.vin.size(); i++) {
        if (!HaveCoin(tx.vin[i].prevout)) {
            return false;
        }
    }

    return true;
}

//获取交易优先级
//tx(in):获取该交易的优先级； height:交易的父块高度；inChainInputValue(out):交易引用输出的总金额。
double CCoinsViewCache::GetPriority(const CTransaction &tx, int nHeight,
                                    Amount &inChainInputValue) const {
    inChainInputValue = Amount(0);
    if (tx.IsCoinBase()) {
        return 0.0;
    }
    double dResult = 0.0;
    for (const CTxIn &txin : tx.vin) {
        //1. 获取preOut
        const Coin &coin = AccessCoin(txin.prevout);
        if (coin.IsSpent()) {
            continue;
        }
        //2. 查看preOut对应的高度是否小于等于 参二(即该引用输出为确认的交易)，
        if (int64_t(coin.GetHeight()) <= nHeight) {
            // 金额*高度差
            dResult += double(coin.GetTxOut().nValue.GetSatoshis()) *
                       (nHeight - coin.GetHeight());
            inChainInputValue += coin.GetTxOut().nValue;
        }
    }
    return tx.ComputePriority(dResult);
}

// TODO: merge with similar definition in undo.h.
static const size_t MAX_OUTPUTS_PER_TX =
    MAX_TX_SIZE / ::GetSerializeSize(CTxOut(), SER_NETWORK, PROTOCOL_VERSION);

// 通过交易ID访问UTXO，并返回查找的coin
const Coin &AccessByTxid(const CCoinsViewCache &view, const uint256 &txid) {
    COutPoint iter(txid, 0);

    // 引用输出的索引符合规则。
    while (iter.n < MAX_OUTPUTS_PER_TX) {
        // 通过构造的outpoint访问UTXO集合，获取coin
        const Coin &alternate = view.AccessCoin(iter);
        // 如果UTXO集合中存在该coin，就将它返回
        if (!alternate.IsSpent()) {
            return alternate;
        }
        ++iter.n;
    }

    return coinEmpty;
}
