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
        // 如果该UTXO已被花费，就将该UTXO flag设置为FRESH；标识该UTXO要下一轮要从缓存中被删除。
        // 注意，此处只是从缓存中删除，而不是从数据库中删除。
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
    //1. 将要添加的UTXO一定是未花费的。
    assert(!coin.IsSpent());
    //2. 且它的脚本一定是可以花费的，才可以添加进UTXO集合中。类似的OP_RETURN这种的烧钱脚本不可以加入UTXO集合中
    if (coin.GetTxOut().scriptPubKey.IsUnspendable()) {
        return;
    }
    CCoinsMap::iterator it;
    bool inserted;
    //3. 将outpoint先插入 缓存中
    std::tie(it, inserted) =
        cacheCoins.emplace(std::piecewise_construct,
                           std::forward_as_tuple(outpoint), std::tuple<>());
    bool fresh = false;
    //4. 插入失败，
    if (!inserted) {
        cachedCoinsUsage -= it->second.coin.DynamicMemoryUsage();
    }
    //5. 是否可能重写。不可能重写，进入下列条件
    if (!possible_overwrite) {
        //6. 此时 队祖的第二个位置应该是不可以花费的交易，因为上一步只插入了key(即outpoint)，下一步才会将对应的coin插入。
        if (!it->second.coin.IsSpent()) {
            throw std::logic_error(
                "Adding new coin that replaces non-pruned entry");
        }
        //7. 此时如果是新的coin，flags = 0；则fresh = true. 没有设置DIRTY时，fresh为true.
        fresh = !(it->second.flags & CCoinsCacheEntry::DIRTY);
    }
    //8. 将这个coin插入 队组中。
    it->second.coin = std::move(coin);
    //9. 设置这个coin对应的flag，如果为新币(即UTXO集合中以前灭有的)，它的flag应该是 DIRTY|FRESH。
    // 如果非新币，它的flag，应该或上 DIRTY。  // 1 和 3
    it->second.flags |=
        CCoinsCacheEntry::DIRTY | (fresh ? CCoinsCacheEntry::FRESH : 0);
    //10. 更新UTXO的内存使用量
    cachedCoinsUsage += it->second.coin.DynamicMemoryUsage();
}

//为当前交易的所有输出构造UTXO，然后插入UTXO集合中。
//cache(in/out): 将要添加的UTXO集合。 tx(in):添加该交易的所有交易输出至参一的UTXO集合中；
// height(in):该交易被打包进块的高度。
void AddCoins(CCoinsViewCache &cache, const CTransaction &tx, int nHeight) {
    //1. 获取交易的标识，以及交易的哈希
    bool fCoinbase = tx.IsCoinBase();
    const uint256 &txid = tx.GetHash();
    //2. 遍历该交易的所有交易输出，构造该交易的所有outpoint。
    for (size_t i = 0; i < tx.vout.size(); ++i) {
        // Pass fCoinbase as the possible_overwrite flag to AddCoin, in order to
        // correctly deal with the pre-BIP30 occurrances of duplicate coinbase
        // transactions.
        // 传递coinbase flag去重载addcoin，以便正确处理BIP30中的重复coinbase交易
        cache.AddCoin(COutPoint(txid, i), Coin(tx.vout[i], nHeight, fCoinbase),
                      fCoinbase);
    }
}

//outpoint(in):引用的交易输出；moveout(out):该引用输出在UTXO集合中的存储币
//标识该outpoint 所对应的UTXO已被花费。即花费该outpoint所对应的UTXO。
//moveout(out) : 需要将它返回，作为该交易的undo信息。
bool CCoinsViewCache::SpendCoin(const COutPoint &outpoint, Coin *moveout) {
    //1. 获取该outpoint在UTXO集合中对应的UTXO。
    CCoinsMap::iterator it = FetchCoin(outpoint);
    if (it == cacheCoins.end()) {
        return false;
    }
    //2. 然后从UTXO集合中删除这个UTXO，同时将这个UTXO写入coin中。
    cachedCoinsUsage -= it->second.coin.DynamicMemoryUsage();
    if (moveout) {
        *moveout = std::move(it->second.coin);
    }
    //3. 如果UTXO的标识位fresh，标识将从缓存中删除这个UTXO。
    if (it->second.flags & CCoinsCacheEntry::FRESH) {
        cacheCoins.erase(it);       //从缓存中删除该交易
    } else {
        // 如果没有标识fresh，则将这个UTXO的flag设置为dirty，标识被一个交易花费。
        it->second.flags |= CCoinsCacheEntry::DIRTY;
        // 设置该UTXO已被花费，该UTXO现在存储在缓存中
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

// 查看一个outpoint是否存在于 view的缓存中
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
            //不在父视图中，进入该条件。
            if (itUs == cacheCoins.end()) {
                // The parent cache does not have an entry, while the child does
                // We can ignore it if it's both FRESH and pruned in the child
                // 父缓存中没有这个条目，如果该条目的孩子同时处于FRESH 和 花费了的状态，可以忽略该条目。
                if (!(it->second.flags & CCoinsCacheEntry::FRESH &&
                      it->second.coin.IsSpent())) {
                    // Otherwise we will need to create it in the parent and
                    // move the data up and mark it as dirty
                    // 不存在与父视图中，且将该条目未被设置为 FRESH，或未花费； 则将该条目插入父视图的缓存中
                    // 注意：此时entry的Flag为0；下面给它设置为DIRTY。
                    CCoinsCacheEntry &entry = cacheCoins[it->first];
                    entry.coin = std::move(it->second.coin);
                    cachedCoinsUsage += entry.coin.DynamicMemoryUsage();
                    entry.flags = CCoinsCacheEntry::DIRTY;
                    // We can mark it FRESH in the parent if it was FRESH in the
                    // child. Otherwise it might have just been flushed from the
                    // parent's cache and already exist in the grandparent
                    // 如果它被设置为FRESH，则也可以在父视图的缓存中设置它为FRESH。
                    if (it->second.flags & CCoinsCacheEntry::FRESH)
                        entry.flags |= CCoinsCacheEntry::FRESH;
                }
            } else {
                //存在于父视图中
                // Assert that the child cache entry was not marked FRESH if the
                // parent cache entry has unspent outputs. If this ever happens,
                // it means the FRESH flag was misapplied and there is a logic
                // error in the calling code.
                // 该Flag设置为FRESH；并且该coin在父缓存中未被花费
                if ((it->second.flags & CCoinsCacheEntry::FRESH) &&
                    !itUs->second.coin.IsSpent())
                    throw std::logic_error("FRESH flag misapplied to cache "
                                           "entry for base transaction with "
                                           "spendable outputs");

                // Found the entry in the parent cache
                // 父缓存中的Flag被设置为FRESH，且子缓存中的该coin被花费， 普通交易
                if ((itUs->second.flags & CCoinsCacheEntry::FRESH) &&
                    it->second.coin.IsSpent()) {
                    // The grandparent does not have an entry, and the child is
                    // modified and being pruned. This means we can just delete
                    // it from the parent.
                    cachedCoinsUsage -= itUs->second.coin.DynamicMemoryUsage();
                    cacheCoins.erase(itUs);
                } else {
                    //将这个coin 移动到腹肌和中，并设置腹肌和中coin的条目为DIRTY
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

//将 参数中的输出从 缓存中去除。
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

// 获取交易输入对应的 coin，并返回coin 中对应的锁定脚本。即返回这个交易输入对应的交易输出。
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
//tx(in):获取该交易的优先级； height:当前主链的高度；inChainInputValue(out):交易引用输出的总金额。
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
            // 引用输出的金额 * 高度差(币的确认高度与当前主链的高度差)
            dResult += double(coin.GetTxOut().nValue.GetSatoshis()) *
                       (nHeight - coin.GetHeight());
            inChainInputValue += coin.GetTxOut().nValue;
        }
    }
    //计算交易的优先级； 结合它花费比的高度和金额；与这个值成正比。
    return tx.ComputePriority(dResult);
}

// TODO: merge with similar definition in undo.h.
static const size_t MAX_OUTPUTS_PER_TX =
    MAX_TX_SIZE / ::GetSerializeSize(CTxOut(), SER_NETWORK, PROTOCOL_VERSION);

// 通过交易ID访问UTXO集合，并返回该交易的最小索引的未花费输出。
const Coin &AccessByTxid(const CCoinsViewCache &view, const uint256 &txid) {
    COutPoint iter(txid, 0);

    // 查询该交易输出
    while (iter.n < MAX_OUTPUTS_PER_TX) {
        // 通过构造的outpoint访问UTXO集合，获取coin
        const Coin &alternate = view.AccessCoin(iter);
        // 如果UTXO集合中存在该coin，且coin未被花费，就将它返回
        if (!alternate.IsSpent()) {
            return alternate;
        }
        ++iter.n;
    }

    return coinEmpty;
}
