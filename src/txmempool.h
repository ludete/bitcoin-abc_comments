// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_TXMEMPOOL_H
#define BITCOIN_TXMEMPOOL_H

#include <map>
#include <memory>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "amount.h"
#include "coins.h"
#include "indirectmap.h"
#include "primitives/transaction.h"
#include "random.h"
#include "sync.h"

#undef foreach
#include "boost/multi_index/hashed_index.hpp"
#include "boost/multi_index/ordered_index.hpp"
#include "boost/multi_index_container.hpp"

#include <boost/signals2/signal.hpp>

class CAutoFile;
class CBlockIndex;

inline double AllowFreeThreshold() {
    return COIN.GetSatoshis() * 144 / 250;
}

//允许免费中继该交易
inline bool AllowFree(double dPriority) {
    // Large (in bytes) low-priority (new, small-coin) transactions need a fee.
    // 最低的优先级交易费，必须大于该值的交易，才会被打包进块中
    return dPriority > AllowFreeThreshold();
}

/**
 * Fake height value used in Coins to signify they are only in the memory
 * pool(since 0.8)
 */
static const uint32_t MEMPOOL_HEIGHT = 0x7FFFFFFF;

struct LockPoints {
    // Will be set to the blockchain height and median time past values that
    // would be necessary to satisfy all relative locktime constraints (BIP68)
    // of this tx given our view of block chain history
    // 设置块链的高度和中值时间，用来符合相对锁定时间限制(BIP68);
    int height;
    int64_t time;
    // As long as the current chain descends from the highest height block
    // containing one of the inputs used in the calculation, then the cached
    // values are still valid even after a reorg.
    // 只要当前的链从这个块高度下降，该高度的块的一个交易 那么缓存的值在块链重组后仍然有效。
    // 该值标识：当前交易的所有交易输入 中最高的块索引。
    CBlockIndex *maxInputBlock;

    LockPoints() : height(0), time(0), maxInputBlock(nullptr) {}
};

class CTxMemPool;

/** \class CTxMemPoolEntry
 *
 * CTxMemPoolEntry stores data about the corresponding transaction, as well as
 * data about all in-mempool transactions that depend on the transaction
 * ("descendant" transactions).
 *
 * When a new entry is added to the mempool, we update the descendant state
 * (nCountWithDescendants, nSizeWithDescendants, and nModFeesWithDescendants)
 * for all ancestors of the newly added transaction.
 *
 * If updating the descendant state is skipped, we can mark the entry as
 * "dirty", and set nSizeWithDescendants/nModFeesWithDescendants to equal
 * nTxSize/nFee+feeDelta. (This can potentially happen during a reorg, where we
 * limit the amount of work we're willing to do to avoid consuming too much
 * CPU.)
 */

class CTxMemPoolEntry {
private:
    CTransactionRef tx;//交易引用
    //!< Cached to avoid expensive parent-transaction lookups; 缓存交易费，避免进行昂贵的查询。
    Amount nFee;//交易费
    //!< ... and avoid recomputing tx size； 缓存交易大小，避免重复计算；
    size_t nTxSize;
    //!< ... and modified size for priority；计算优先级时，默认交易的每个签名最大有110字节；用一个交易的序列化字节-所有签名大小 = nModSize
    size_t nModSize;
    //!< ... and total memory usage； 该结构总的内存使用量
    size_t nUsageSize;
    //!< Local time when entering the mempool； 该交易进入mempool时的本地时间
    int64_t nTime;
    //!< Priority when entering the mempool；  该交易进入mempool时的优先级
    double entryPriority;
    //!< Chain height when entering the mempool； 交易进入mempool时，主链的高度
    unsigned int entryHeight;
    //!< Sum of all txin values that are already in blockchain； 所有交易输入的总和
    Amount inChainInputValue;
    //!< keep track of transactions that spend a coinbase； 标识该交易是否花费了一个coinbase交易，如果花费了，此处为true.
    bool spendsCoinbase;
    //!< Total sigop plus P2SH sigops count； 所有的操作码加上P2SH的操作码
    int64_t sigOpCount;
    //!< Used for determining the priority of the transaction for mining in a
    //! block  用来决定交易在挖矿时的优先级
    Amount feeDelta;
    //!< Track the height and time at which tx was final；  跟踪每个交易在哪个高度，哪个时间，将为成熟交易，可以打包。
    LockPoints lockPoints;

    // Information about descendants of this transaction that are in the
    // mempool; if we remove this transaction we must remove all of these
    // descendants as well.  if nCountWithDescendants is 0, treat this entry as
    // dirty, and nSizeWithDescendants and nModFeesWithDescendants will not be
    // correct.  在交易池中该交易的后代交易数量；如果移除了该交易，那么也必须移除它所有的后代交易。
    // 当 nCountWithDescendants = 0时，这个字段是不正确的，并且nModFeesWithDescendants和nSizeWithDescendants也不正确。
    // 因为每个交易的该值默认从1开始。
    //!< number of descendant transactions
    uint64_t nCountWithDescendants;
    //!< ... and size
    uint64_t nSizeWithDescendants;
    //!< ... and total fees (all including us)
    Amount nModFeesWithDescendants;

    // Analogous statistics for ancestor transactions  类似的该交易的祖先交易的信息。
    uint64_t nCountWithAncestors;
    uint64_t nSizeWithAncestors;
    Amount nModFeesWithAncestors;
    int64_t nSigOpCountWithAncestors;

public:
    CTxMemPoolEntry(const CTransactionRef &_tx, const Amount _nFee,
                    int64_t _nTime, double _entryPriority,
                    unsigned int _entryHeight, Amount _inChainInputValue,
                    bool spendsCoinbase, int64_t nSigOpsCost, LockPoints lp);

    CTxMemPoolEntry(const CTxMemPoolEntry &other);

    const CTransaction &GetTx() const { return *this->tx; }
    CTransactionRef GetSharedTx() const { return this->tx; }
    /**
     * Fast calculation of lower bound of current priority as update from entry
     * priority. Only inputs that were originally in-chain will age.
     */
    double GetPriority(unsigned int currentHeight) const;
    const Amount GetFee() const { return nFee; }
    size_t GetTxSize() const { return nTxSize; }
    int64_t GetTime() const { return nTime; }
    unsigned int GetHeight() const { return entryHeight; }
    int64_t GetSigOpCount() const { return sigOpCount; }
    Amount GetModifiedFee() const { return nFee + feeDelta; }
    size_t DynamicMemoryUsage() const { return nUsageSize; }
    const LockPoints &GetLockPoints() const { return lockPoints; }

    // Adjusts the descendant state, if this entry is not dirty.
    void UpdateDescendantState(int64_t modifySize, Amount modifyFee,
                               int64_t modifyCount);
    // Adjusts the ancestor state
    void UpdateAncestorState(int64_t modifySize, Amount modifyFee,
                             int64_t modifyCount, int modifySigOps);
    // Updates the fee delta used for mining priority score, and the
    // modified fees with descendants.
    void UpdateFeeDelta(Amount feeDelta);
    // Update the LockPoints after a reorg
    void UpdateLockPoints(const LockPoints &lp);

    uint64_t GetCountWithDescendants() const { return nCountWithDescendants; }
    uint64_t GetSizeWithDescendants() const { return nSizeWithDescendants; }
    Amount GetModFeesWithDescendants() const { return nModFeesWithDescendants; }

    bool GetSpendsCoinbase() const { return spendsCoinbase; }

    uint64_t GetCountWithAncestors() const { return nCountWithAncestors; }
    uint64_t GetSizeWithAncestors() const { return nSizeWithAncestors; }
    Amount GetModFeesWithAncestors() const { return nModFeesWithAncestors; }
    int64_t GetSigOpCountWithAncestors() const {
        return nSigOpCountWithAncestors;
    }

    //!< Index in mempool's vTxHashes
    mutable size_t vTxHashesIdx;
};

// Helpers for modifying CTxMemPool::mapTx, which is a boost multi_index.
struct update_descendant_state {
    update_descendant_state(int64_t _modifySize, Amount _modifyFee,
                            int64_t _modifyCount)
        : modifySize(_modifySize), modifyFee(_modifyFee),
          modifyCount(_modifyCount) {}

    void operator()(CTxMemPoolEntry &e) {
        e.UpdateDescendantState(modifySize, modifyFee, modifyCount);
    }

private:
    int64_t modifySize;
    Amount modifyFee;
    int64_t modifyCount;
};

struct update_ancestor_state {
    update_ancestor_state(int64_t _modifySize, Amount _modifyFee,
                          int64_t _modifyCount, int64_t _modifySigOpsCost)
        : modifySize(_modifySize), modifyFee(_modifyFee),
          modifyCount(_modifyCount), modifySigOpsCost(_modifySigOpsCost) {}

    void operator()(CTxMemPoolEntry &e) {
        e.UpdateAncestorState(modifySize, modifyFee, modifyCount,
                              modifySigOpsCost);
    }

private:
    int64_t modifySize;
    Amount modifyFee;
    int64_t modifyCount;
    int64_t modifySigOpsCost;
};

struct update_fee_delta {
    update_fee_delta(Amount _feeDelta) : feeDelta(_feeDelta) {}

    void operator()(CTxMemPoolEntry &e) { e.UpdateFeeDelta(feeDelta); }

private:
    Amount feeDelta;
};

struct update_lock_points {
    update_lock_points(const LockPoints &_lp) : lp(_lp) {}

    void operator()(CTxMemPoolEntry &e) { e.UpdateLockPoints(lp); }

private:
    const LockPoints &lp;
};

// extracts a TxMemPoolEntry's transaction hash
struct mempoolentry_txid {
    typedef uint256 result_type;
    result_type operator()(const CTxMemPoolEntry &entry) const {
        return entry.GetTx().GetId();
    }
};

/** \class CompareTxMemPoolEntryByDescendantScore
 *
 *  Sort an entry by max(score/size of entry's tx, score/size with all
 * descendants).
 */
class CompareTxMemPoolEntryByDescendantScore {
public:
    bool operator()(const CTxMemPoolEntry &a, const CTxMemPoolEntry &b) {
        bool fUseADescendants = UseDescendantScore(a);
        bool fUseBDescendants = UseDescendantScore(b);

        double aModFee = (fUseADescendants ? a.GetModFeesWithDescendants()
                                           : a.GetModifiedFee())
                             .GetSatoshis();
        double aSize =
            fUseADescendants ? a.GetSizeWithDescendants() : a.GetTxSize();

        double bModFee = (fUseBDescendants ? b.GetModFeesWithDescendants()
                                           : b.GetModifiedFee())
                             .GetSatoshis();
        double bSize =
            fUseBDescendants ? b.GetSizeWithDescendants() : b.GetTxSize();

        // Avoid division by rewriting (a/b > c/d) as (a*d > c*b).
        double f1 = aModFee * bSize;
        double f2 = aSize * bModFee;

        if (f1 == f2) {
            return a.GetTime() >= b.GetTime();
        }
        return f1 < f2;
    }

    // Calculate which score to use for an entry (avoiding division).
    bool UseDescendantScore(const CTxMemPoolEntry &a) {
        double f1 = double(a.GetSizeWithDescendants() *
                           a.GetModifiedFee().GetSatoshis());
        double f2 =
            double(a.GetTxSize() * a.GetModFeesWithDescendants().GetSatoshis());
        return f2 > f1;
    }
};

/** \class CompareTxMemPoolEntryByScore
 *
 *  Sort by score of entry ((fee+delta)/size) in descending order
 */
class CompareTxMemPoolEntryByScore {
public:
    bool operator()(const CTxMemPoolEntry &a, const CTxMemPoolEntry &b) {
        double f1 = double(b.GetTxSize() * a.GetModifiedFee().GetSatoshis());
        double f2 = double(a.GetTxSize() * b.GetModifiedFee().GetSatoshis());
        if (f1 == f2) {
            return b.GetTx().GetId() < a.GetTx().GetId();
        }
        return f1 > f2;
    }
};

class CompareTxMemPoolEntryByEntryTime {
public:
    bool operator()(const CTxMemPoolEntry &a, const CTxMemPoolEntry &b) {
        return a.GetTime() < b.GetTime();
    }
};

class CompareTxMemPoolEntryByAncestorFee {
public:
    bool operator()(const CTxMemPoolEntry &a, const CTxMemPoolEntry &b) {
        double aFees = double(a.GetModFeesWithAncestors().GetSatoshis());
        double aSize = a.GetSizeWithAncestors();

        double bFees = double(b.GetModFeesWithAncestors().GetSatoshis());
        double bSize = b.GetSizeWithAncestors();

        // Avoid division by rewriting (a/b > c/d) as (a*d > c*b).
        double f1 = aFees * bSize;
        double f2 = aSize * bFees;

        if (f1 == f2) {
            return a.GetTx().GetId() < b.GetTx().GetId();
        }

        return f1 > f2;
    }
};

// Multi_index tag names
struct descendant_score {};
struct entry_time {};
struct mining_score {};
struct ancestor_score {};

class CBlockPolicyEstimator;

/**
 * Information about a mempool transaction.
 * 交易池中条目的信息
 */
struct TxMempoolInfo {
    /** The transaction itself 交易*/
    CTransactionRef tx;

    /** Time the transaction entered the mempool. 交易进入交易池的时间*/
    int64_t nTime;

    /** Feerate of the transaction. 该交易费率*/
    CFeeRate feeRate;

    /** The fee delta. */
    Amount nFeeDelta;
};

/**
 * Reason why a transaction was removed from the mempool, this is passed to the
 * notification signal.
 */
enum class MemPoolRemovalReason {
    //! Manually removed or unknown reason
    UNKNOWN = 0,
    //! Expired from mempool
    EXPIRY,
    //! Removed in size limiting
    SIZELIMIT,
    //! Removed for reorganization
    REORG,
    //! Removed for block
    BLOCK,
    //! Removed for conflict with in-block transaction
    CONFLICT,
    //! Removed for replacement
    REPLACED
};

class SaltedTxidHasher {
private:
    /** Salt */
    const uint64_t k0, k1;

public:
    SaltedTxidHasher();

    size_t operator()(const uint256 &txid) const {
        return SipHashUint256(k0, k1, txid);
    }
};

/**
 * CTxMemPool stores valid-according-to-the-current-best-chain transactions that
 * may be included in the next block.
 *
 * Transactions are added when they are seen on the network (or created by the
 * local node), but not all transactions seen are added to the pool. For
 * example, the following new transactions will not be added to the mempool:
 * - a transaction which doesn't meet the minimum fee requirements.
 * - a new transaction that double-spends an input of a transaction already in
 * the pool where the new transaction does not meet the Replace-By-Fee
 * requirements as defined in BIP 125.
 * - a non-standard transaction.
 *
 * CTxMemPool::mapTx, and CTxMemPoolEntry bookkeeping:
 *
 * mapTx is a boost::multi_index that sorts the mempool on 4 criteria:
 * - transaction hash
 * - feerate [we use max(feerate of tx, feerate of tx with all descendants)]
 * - time in mempool
 * - mining score (feerate modified by any fee deltas from
 * PrioritiseTransaction)
 *
 * Note: the term "descendant" refers to in-mempool transactions that depend on
 * this one, while "ancestor" refers to in-mempool transactions that a given
 * transaction depends on.
 *
 * In order for the feerate sort to remain correct, we must update transactions
 * in the mempool when new descendants arrive. To facilitate this, we track the
 * set of in-mempool direct parents and direct children in mapLinks. Within each
 * CTxMemPoolEntry, we track the size and fees of all descendants.
 *
 * Usually when a new transaction is added to the mempool, it has no in-mempool
 * children (because any such children would be an orphan). So in
 * addUnchecked(), we:
 * - update a new entry's setMemPoolParents to include all in-mempool parents
 * - update the new entry's direct parents to include the new tx as a child
 * - update all ancestors of the transaction to include the new tx's size/fee
 *
 * When a transaction is removed from the mempool, we must:
 * - update all in-mempool parents to not track the tx in setMemPoolChildren
 * - update all ancestors to not include the tx's size/fees in descendant state
 * - update all in-mempool children to not include it as a parent
 *
 * These happen in UpdateForRemoveFromMempool(). (Note that when removing a
 * transaction along with its descendants, we must calculate that set of
 * transactions to be removed before doing the removal, or else the mempool can
 * be in an inconsistent state where it's impossible to walk the ancestors of a
 * transaction.)
 *
 * In the event of a reorg, the assumption that a newly added tx has no
 * in-mempool children is false.  In particular, the mempool is in an
 * inconsistent state while new transactions are being added, because there may
 * be descendant transactions of a tx coming from a disconnected block that are
 * unreachable from just looking at transactions in the mempool (the linking
 * transactions may also be in the disconnected block, waiting to be added).
 * Because of this, there's not much benefit in trying to search for in-mempool
 * children in addUnchecked(). Instead, in the special case of transactions
 * being added from a disconnected block, we require the caller to clean up the
 * state, to account for in-mempool, out-of-block descendants for all the
 * in-block transactions by calling UpdateTransactionsFromBlock(). Note that
 * until this is called, the mempool state is not consistent, and in particular
 * mapLinks may not be correct (and therefore functions like
 * CalculateMemPoolAncestors() and CalculateDescendants() that rely on them to
 * walk the mempool are not generally safe to use).
 *
 * Computational limits:
 *
 * Updating all in-mempool ancestors of a newly added transaction can be slow,
 * if no bound exists on how many in-mempool ancestors there may be.
 * CalculateMemPoolAncestors() takes configurable limits that are designed to
 * prevent these calculations from being too CPU intensive.
 *
 * Adding transactions from a disconnected block can be very time consuming,
 * because we don't have a way to limit the number of in-mempool descendants. To
 * bound CPU processing, we limit the amount of work we're willing to do to
 * properly update the descendant information for a tx being added from a
 * disconnected block. If we would exceed the limit, then we instead mark the
 * entry as "dirty", and set the feerate for sorting purposes to be equal the
 * feerate of the transaction without any descendants.
 * 交易内存池，保存所有在当前主链上有效的交易。
 * 当交易在网络上广播之后，就会被加进交易池。
 * 但并不是所有的交易都会被加入，
 * 例如交易费太小的，或者“双花”的交易或者非标准交易。
 * 内存池中通过一个boost::multi_index类型的变量mapTx来排序所有交易，
 * 按照下面四个标准：
 * -交易hash
 * -交易费（包括所有子孙交易）
 * -在mempool中的时间
 * -挖矿分数
 * 为了保证交易费的正确性，当新交易被加进mempool时，我们必须更新
 * 该交易的所有祖先交易信息，而这个操作可能会导致处理速度变慢，
 * 所以必须对更需祖先的数量进行限制。
 */
class CTxMemPool {
private:
    //!< Value n means that n times in 2^32 we check.
    uint32_t nCheckFrequency;       //设置完整性检查
    unsigned int nTransactionsUpdated;
    CBlockPolicyEstimator *minerPolicyEstimator;

    //!< sum of all mempool tx's virtual sizes.
    uint64_t totalTxSize;
    //!< sum of dynamic memory usage of all the map elements (NOT the maps
    //! themselves)
    uint64_t cachedInnerUsage;

    mutable int64_t lastRollingFeeUpdate;       //最后一次更新矿池手续费的时间
    mutable bool blockSinceLastRollingFeeBump;
    //!< minimum fee to get into the pool, decreases exponentially 进入交易池的最低手续费，成倍降低
    mutable double rollingMinimumFeeRate;

    void trackPackageRemoved(const CFeeRate &rate);

public:
    // public only for testing； 12小时
    static const int ROLLING_FEE_HALFLIFE = 60 * 60 * 12;

    typedef boost::multi_index_container<
        CTxMemPoolEntry, boost::multi_index::indexed_by<
                             // sorted by txid
                             boost::multi_index::hashed_unique<
                                 mempoolentry_txid, SaltedTxidHasher>,
                             // sorted by fee rate
                             boost::multi_index::ordered_non_unique<
                                 boost::multi_index::tag<descendant_score>,
                                 boost::multi_index::identity<CTxMemPoolEntry>,
                                 CompareTxMemPoolEntryByDescendantScore>,
                             // sorted by entry time
                             boost::multi_index::ordered_non_unique<
                                 boost::multi_index::tag<entry_time>,
                                 boost::multi_index::identity<CTxMemPoolEntry>,
                                 CompareTxMemPoolEntryByEntryTime>,
                             // sorted by score (for mining prioritization)
                             boost::multi_index::ordered_unique<
                                 boost::multi_index::tag<mining_score>,
                                 boost::multi_index::identity<CTxMemPoolEntry>,
                                 CompareTxMemPoolEntryByScore>,
                             // sorted by fee rate with ancestors
                             boost::multi_index::ordered_non_unique<
                                 boost::multi_index::tag<ancestor_score>,
                                 boost::multi_index::identity<CTxMemPoolEntry>,
                                 CompareTxMemPoolEntryByAncestorFee>>>
        indexed_transaction_set;

    mutable CCriticalSection cs;
    indexed_transaction_set mapTx;

    typedef indexed_transaction_set::nth_index<0>::type::iterator txiter;
    //!< All tx hashes/entries in mapTx, in random order
    std::vector<std::pair<uint256, txiter>> vTxHashes;

    struct CompareIteratorByHash {
        bool operator()(const txiter &a, const txiter &b) const {
            return a->GetTx().GetId() < b->GetTx().GetId();
        }
    };
    typedef std::set<txiter, CompareIteratorByHash> setEntries;

    const setEntries &GetMemPoolParents(txiter entry) const;
    const setEntries &GetMemPoolChildren(txiter entry) const;

private:
    typedef std::map<txiter, setEntries, CompareIteratorByHash> cacheMap;

    struct TxLinks {
        setEntries parents;
        setEntries children;
    };

    typedef std::map<txiter, TxLinks, CompareIteratorByHash> txlinksMap;
    txlinksMap mapLinks;

    void UpdateParent(txiter entry, txiter parent, bool add);
    void UpdateChild(txiter entry, txiter child, bool add);

    std::vector<indexed_transaction_set::const_iterator>
    GetSortedDepthAndScore() const;

public:
    indirectmap<COutPoint, const CTransaction *> mapNextTx;     //存储一个交易花费的引用输出，和它的交易。
    std::map<uint256, std::pair<double, Amount>> mapDeltas;     //key : 交易的哈希；value : Amount 金额；double : 优先级；

    /** Create a new CTxMemPool.
     */
    CTxMemPool(const CFeeRate &_minReasonableRelayFee);
    ~CTxMemPool();

    /**
     * If sanity-checking is turned on, check makes sure the pool is consistent
     * (does not contain two transactions that spend the same inputs, all inputs
     * are in the mapNextTx array). If sanity-checking is turned off, check does
     * nothing.
     */
    void check(const CCoinsViewCache *pcoins) const;
    void setSanityCheck(double dFrequency = 1.0) {
        nCheckFrequency = dFrequency * 4294967295.0;
    }

    // addUnchecked must updated state for all ancestors of a given transaction,
    // to track size/count of descendant transactions. First version of
    // addUnchecked can be used to have it call CalculateMemPoolAncestors(), and
    // then invoke the second version.
    bool addUnchecked(const uint256 &hash, const CTxMemPoolEntry &entry,
                      bool validFeeEstimate = true);
    bool addUnchecked(const uint256 &hash, const CTxMemPoolEntry &entry,
                      setEntries &setAncestors, bool validFeeEstimate = true);

    void removeRecursive(
        const CTransaction &tx,
        MemPoolRemovalReason reason = MemPoolRemovalReason::UNKNOWN);
    void removeForReorg(const CCoinsViewCache *pcoins,
                        unsigned int nMemPoolHeight, int flags);
    void removeConflicts(const CTransaction &tx);
    void removeForBlock(const std::vector<CTransactionRef> &vtx,
                        unsigned int nBlockHeight);

    void clear();
    // lock free
    void _clear();
    bool CompareDepthAndScore(const uint256 &hasha, const uint256 &hashb);
    void queryHashes(std::vector<uint256> &vtxid);
    bool isSpent(const COutPoint &outpoint);
    unsigned int GetTransactionsUpdated() const;
    void AddTransactionsUpdated(unsigned int n);
    /**
     * Check that none of this transactions inputs are in the mempool, and thus
     * the tx is not dependent on other mempool transactions to be included in a
     * block.
     */
    bool HasNoInputsOf(const CTransaction &tx) const;

    /** Affect CreateNewBlock prioritisation of transactions 影响 CreateNewBlock交易的优先级*/
    void PrioritiseTransaction(const uint256 hash, const std::string strHash,
                               double dPriorityDelta, const Amount nFeeDelta);
    void ApplyDeltas(const uint256 hash, double &dPriorityDelta,
                     Amount &nFeeDelta) const;
    void ClearPrioritisation(const uint256 hash);

public:
    /**
     * Remove a set of transactions from the mempool. If a transaction is in
     * this set, then all in-mempool descendants must also be in the set, unless
     * this transaction is being removed for being in a block. Set
     * updateDescendants to true when removing a tx that was in a block, so that
     * any in-mempool descendants have their ancestor state updated.
     * 移除交易池中的一个交易集合。如果一个交易在这个删除集合中，那么这个交易在交易池中的所有的后代
     * 交易都必须在这个集合中。除非因为接受了一个区块而需要删除区块中的交易，所以所有交易池中以
     * 这个交易作为祖先交易的后代交易都必须更新他们的祖先交易的状态。
     */
    void
    RemoveStaged(setEntries &stage, bool updateDescendants,
                 MemPoolRemovalReason reason = MemPoolRemovalReason::UNKNOWN);

    /**
     * When adding transactions from a disconnected block back to the mempool,
     * new mempool entries may have children in the mempool (which is generally
     * not the case when otherwise adding transactions).
     * UpdateTransactionsFromBlock() will find child transactions and update the
     * descendant state for each transaction in hashesToUpdate (excluding any
     * child transactions present in hashesToUpdate, which are already accounted
     * for).  Note: hashesToUpdate should be the set of transactions from the
     * disconnected block that have been accepted back into the mempool.
     * 当把一个拒绝的块中的交易添加回mempool时，mempool中可能存在这些交易的子交易。
     *
     */
    void
    UpdateTransactionsFromBlock(const std::vector<uint256> &hashesToUpdate);

    /**
     * Try to calculate all in-mempool ancestors of entry.
     *  (these are all calculated including the tx itself)
     *  limitAncestorCount = max number of ancestors
     *  limitAncestorSize = max size of ancestors
     *  limitDescendantCount = max number of descendants any ancestor can have
     *  limitDescendantSize = max size of descendants any ancestor can have
     *  errString = populated with error reason if any limits are hit
     * fSearchForParents = whether to search a tx's vin for in-mempool parents,
     * or look up parents from mapLinks. Must be true for entries not in the
     * mempool
     * 计算交易池中关于一个交易的所有祖先。注意：此时参数二作为传出参数，不包含当前传入的交易。与CalculateDescendants 相反。
     */
    bool CalculateMemPoolAncestors(
        const CTxMemPoolEntry &entry, setEntries &setAncestors,
        uint64_t limitAncestorCount, uint64_t limitAncestorSize,
        uint64_t limitDescendantCount, uint64_t limitDescendantSize,
        std::string &errString, bool fSearchForParents = true) const;

    /**
     * Populate setDescendants with all in-mempool descendants of hash.
     * Assumes that setDescendants includes all in-mempool descendants of
     * anything already in it.
     * 计算交易池中关于一个交易的所有后代交易。注意：此时参数二作为传出参数，包含当前传入的交易。与CalculateMemPoolAncestors 相反。
     * */
    void CalculateDescendants(txiter it, setEntries &setDescendants);

    /**
     * The minimum fee to get into the mempool, which may itself not be enough
     * for larger-sized transactions. The incrementalRelayFee policy variable is
     * used to bound the time it takes the fee rate to go back down all the way
     * to 0. When the feerate would otherwise be half of this, it is set to 0
     * instead.
     *
     */
    CFeeRate GetMinFee(size_t sizelimit) const;

    /**
     * Remove transactions from the mempool until its dynamic size is <=
     * sizelimit. pvNoSpendsRemaining, if set, will be populated with the list
     * of outpoints which are not in mempool which no longer have any spends in
     * this mempool.
     * 从交易池中移除交易，直到交易池的内存小号达到指定大小。
     * 如果参数二不为空，标识想要知道 这些删除的交易中，直接依赖UTXO集合的引用。当这个函数返回时，
     * 可以在外部依据此信息，对UTXO集合进行修改，因为这些引用输出没有被花费。
     */
    void TrimToSize(size_t sizelimit,
                    std::vector<COutPoint> *pvNoSpendsRemaining = nullptr);

    /** Expire all transaction (and their dependencies) in the mempool older
     * than time. Return the number of removed transactions.
     * 删除交易池中指定时间之前的交易，以及它所有的后代交易，并返回删除的总交易个数。
     * */
    int Expire(int64_t time);

    /** Returns false if the transaction is in the mempool and not within the
     * chain limit specified.
     * 如果交易在交易池中，但是不在当前链的限制之内，返回false
     * */
    bool TransactionWithinChainLimit(const uint256 &txid,
                                     size_t chainLimit) const;

    unsigned long size() {
        LOCK(cs);
        return mapTx.size();
    }

    uint64_t GetTotalTxSize() {
        LOCK(cs);
        return totalTxSize;
    }

    bool exists(uint256 hash) const {
        LOCK(cs);
        return mapTx.count(hash) != 0;
    }
    0xc637c4601bb942effe5bf7f5d6551968b94da8c2
    bool exists(const COutPoint &outpoint) const {
        LOCK(cs);
        auto it = mapTx.find(outpoint.hash);
        return it != mapTx.end() && outpoint.n < it->GetTx().vout.size();
    }

    CTransactionRef get(const uint256 &hash) const;
    TxMempoolInfo info(const uint256 &hash) const;
    std::vector<TxMempoolInfo> infoAll() const;

    /**
     * Estimate fee rate needed to get into the next nBlocks. If no answer can
     * be given at nBlocks, return an estimate at the lowest number of blocks
     * where one can be given.
     */
    CFeeRate estimateSmartFee(int nBlocks,
                              int *answerFoundAtBlocks = nullptr) const;

    /** Estimate fee rate needed to get into the next nBlocks */
    CFeeRate estimateFee(int nBlocks) const;

    /**
     * Estimate priority needed to get into the next nBlocks. If no answer can
     * be given at nBlocks, return an estimate at the lowest number of blocks
     * where one can be given.
     */
    double estimateSmartPriority(int nBlocks,
                                 int *answerFoundAtBlocks = nullptr) const;

    /** Estimate priority needed to get into the next nBlocks */
    double estimatePriority(int nBlocks) const;

    /** Write/Read estimates to disk */
    bool WriteFeeEstimates(CAutoFile &fileout) const;
    bool ReadFeeEstimates(CAutoFile &filein);

    size_t DynamicMemoryUsage() const;

    boost::signals2::signal<void(CTransactionRef)> NotifyEntryAdded;   //添加交易的信号
    boost::signals2::signal<void(CTransactionRef, MemPoolRemovalReason)>
        NotifyEntryRemoved;     //移除交易的信号； 参一：操作的交易； 参二：操作的原因

private:
    /**
     * UpdateForDescendants is used by UpdateTransactionsFromBlock to update the
     * descendants for a single transaction that has been added to the mempool
     * but may have child transactions in the mempool, eg during a chain reorg.
     * setExclude is the set of descendant transactions in the mempool that must
     * not be accounted for (because any descendants in setExclude were added to
     * the mempool after the transaction being updated and hence their state is
     * already reflected in the parent state).
     *
     * cachedDescendants will be updated with the descendants of the transaction
     * being updated, so that future invocations don't need to walk the same
     * transaction again, if encountered in another transaction chain.
     */
    void UpdateForDescendants(txiter updateIt, cacheMap &cachedDescendants,
                              const std::set<uint256> &setExclude);
    /** Update ancestors of hash to add/remove it as a descendant transaction.
     */
    void UpdateAncestorsOf(bool add, txiter hash, setEntries &setAncestors);
    /** Set ancestor state for an entry */
    void UpdateEntryForAncestors(txiter it, const setEntries &setAncestors);
    /**
     * For each transaction being removed, update ancestors and any direct
     * children. If updateDescendants is true, then also update in-mempool
     * descendants' ancestor state.
     * 对于每个移除的交易，更新它的祖先，和所有的直接的子交易。如果updateDescendants 为true，
     * 则更新交易池中 它的所有的后代交易。
     */
    void UpdateForRemoveFromMempool(const setEntries &entriesToRemove,
                                    bool updateDescendants);
    /** Sever link between specified transaction and direct children. */
    void UpdateChildrenForRemoval(txiter entry);

    /**
     * Before calling removeUnchecked for a given transaction,
     * UpdateForRemoveFromMempool must be called on the entire (dependent) set
     * of transactions being removed at the same time. We use each
     * CTxMemPoolEntry's setMemPoolParents in order to walk ancestors of a given
     * transaction that is removed, so we can't remove intermediate transactions
     * in a chain before we've updated all the state for the removal.
     */
    void removeUnchecked(txiter entry, MemPoolRemovalReason reason =
                                           MemPoolRemovalReason::UNKNOWN);
};

/**
 * CCoinsView that brings transactions from a memorypool into view.
 * It does not check for spendings by memory pool transactions.
 */
class CCoinsViewMemPool : public CCoinsViewBacked {
protected:
    const CTxMemPool &mempool;

public:
    CCoinsViewMemPool(CCoinsView *baseIn, const CTxMemPool &mempoolIn);
    bool GetCoin(const COutPoint &outpoint, Coin &coin) const;
    bool HaveCoin(const COutPoint &outpoint) const;
};

// We want to sort transactions by coin age priority； 通过花费的币的年龄的优先级来排序交易
// priority = amount * spendHeightDifference;
typedef std::pair<double, CTxMemPool::txiter> TxCoinAgePriority;

//交易金额优先级 比较
struct TxCoinAgePriorityCompare {
    bool operator()(const TxCoinAgePriority &a, const TxCoinAgePriority &b) {
        // 1. 如果两个交易  币的优先级相同，则比较
        if (a.first == b.first) {
            // Reverse order to make sort less than
            return CompareTxMemPoolEntryByScore()(*(b.second), *(a.second));
        }
        return a.first < b.first;
    }
};

#endif // BITCOIN_TXMEMPOOL_H
