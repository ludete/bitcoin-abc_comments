// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CHAIN_H
#define BITCOIN_CHAIN_H

#include "arith_uint256.h"
#include "pow.h"
#include "primitives/block.h"
#include "tinyformat.h"
#include "uint256.h"

#include <vector>

class CBlockFileInfo {
public:
    //!< number of blocks stored in file； 文件中区块的数量
    unsigned int nBlocks;
    //!< number of used bytes of block file 区块文件中的字节数
    unsigned int nSize;
    //!< number of used bytes in the undo file  undo文件中的字节数
    unsigned int nUndoSize;
    //!< lowest height of block in file  该文件中最低的区块号
    unsigned int nHeightFirst;
    //!< highest height of block in file    该文件中最高的区块号
    unsigned int nHeightLast;
    //!< earliest time of block in file     该文件中最早的区块时间
    uint64_t nTimeFirst;
    //!< latest time of block in file       该文件中最后的区块时间
    uint64_t nTimeLast;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream &s, Operation ser_action) {
        READWRITE(VARINT(nBlocks));
        READWRITE(VARINT(nSize));
        READWRITE(VARINT(nUndoSize));
        READWRITE(VARINT(nHeightFirst));
        READWRITE(VARINT(nHeightLast));
        READWRITE(VARINT(nTimeFirst));
        READWRITE(VARINT(nTimeLast));
    }

    void SetNull() {
        nBlocks = 0;
        nSize = 0;
        nUndoSize = 0;
        nHeightFirst = 0;
        nHeightLast = 0;
        nTimeFirst = 0;
        nTimeLast = 0;
    }

     CBlockFileInfo() { SetNull(); }

    std::string ToString() const;

    /** update statistics (does not update nSize) 更新文件的信息*/
    void AddBlock(unsigned int nHeightIn, uint64_t nTimeIn) {
        if (nBlocks == 0 || nHeightFirst > nHeightIn) {
            nHeightFirst = nHeightIn;
        }
        if (nBlocks == 0 || nTimeFirst > nTimeIn) {
            nTimeFirst = nTimeIn;
        }
        nBlocks++;
        if (nHeightIn > nHeightLast) {
            nHeightLast = nHeightIn;
        }
        if (nTimeIn > nTimeLast) {
            nTimeLast = nTimeIn;
        }
    }
};

struct CDiskBlockPos {
    int nFile;
    unsigned int nPos;

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream &s, Operation ser_action) {
        READWRITE(VARINT(nFile));
        READWRITE(VARINT(nPos));
    }

    CDiskBlockPos() { SetNull(); }

    CDiskBlockPos(int nFileIn, unsigned int nPosIn) {
        nFile = nFileIn;
        nPos = nPosIn;
    }

    friend bool operator==(const CDiskBlockPos &a, const CDiskBlockPos &b) {
        return (a.nFile == b.nFile && a.nPos == b.nPos);
    }

    friend bool operator!=(const CDiskBlockPos &a, const CDiskBlockPos &b) {
        return !(a == b);
    }

    void SetNull() {
        nFile = -1;
        nPos = 0;
    }
    bool IsNull() const { return (nFile == -1); }

    std::string ToString() const {
        return strprintf("CBlockDiskPos(nFile=%i, nPos=%i)", nFile, nPos);
    }
};

//区块的状态
enum BlockStatus : uint32_t {
    //! Unused. 未使用
    BLOCK_VALID_UNKNOWN = 0,

    //! Parsed, version ok, hash satisfies claimed PoW, 1 <= vtx count <= max,
    //! timestamp not in future
    // 解析正确，版本号正确，块哈希符合声明的POW工作量，且交易数目 在一个正确的范围内[1, max]
    // 时间戳不在超出未来的范围。
    BLOCK_VALID_HEADER = 1,     // 01

    //! All parent headers found, difficulty matches, timestamp >= median
    //! previous, checkpoint. Implies all parents are also at least TREE.
    // 标识一个块的块头合法。应该是块的第二个状态，(当在本节点找到一个块的父块，且该块的块头检查合法时，就标识该块的状态为 BLOCK_VALID_TREE)
    // 同时意味着：这个块的所有依赖块的状态都至少为 BLOCK_VALID_TREE
    BLOCK_VALID_TREE = 2,       // 10

    /**
     * Only first tx is coinbase, 2 <= coinbase input script length <= 100,
     * transactions valid, no duplicate txids, sigops, size, merkle root.
     * Implies all parents are at least TREE but not necessarily TRANSACTIONS.
     * When all parent blocks also have TRANSACTIONS, CBlockIndex::nChainTx will
     * be set.
     * 当块的第一个交易未coinbase交易，且coinbase输入脚本长度在 [2,100]区间，所有的交易有效，没有
     * 重复的交易ID，签名操作码，字节，merkle Root正确。则标识该块的状态为 BLOCK_VALID_TRANSACTIONS
     * 当一个块为这个状态时，意味着它的所有的父块的状态至少为BLOCK_VALID_TREE；当所有的父块和它自己都为
     * BLOCK_VALID_TRANSACTIONS这个状态时，CBlockIndex::nChainTx将会被设置为一个有效值。
     */
    BLOCK_VALID_TRANSACTIONS = 3,   //11

    //! Outputs do not overspend inputs, no double spends, coinbase output ok,
    //! no immature coinbase spends, BIP30.
    //! Implies all parents are also at least CHAIN.
    // 输出正确，没有大于输入的输出，没有双重花费，没有coinbase输出，没有不成熟的coinbase花费。
    // 当一个块为这个状态时，意味着它所有的父块至少都为这个状态 BLOCK_VALID_CHAIN。
    BLOCK_VALID_CHAIN = 4,          //100

    //! Scripts & signatures ok. Implies all parents are also at least SCRIPTS.
    // 块中所有的脚本签名都验签通过。当一个块这种状态时，标识它的所有父块至少都为 BLOCK_VALID_SCRIPTS。
    BLOCK_VALID_SCRIPTS = 5,        //101

    //注意上述五个等级，每次设置时，只会出现一个
    //! All validity bits.; 如果一个块的标识等于它，标识这个块已完全验证有效
    BLOCK_VALID_MASK = BLOCK_VALID_HEADER | BLOCK_VALID_TREE |
                       BLOCK_VALID_TRANSACTIONS | BLOCK_VALID_CHAIN |
                       BLOCK_VALID_SCRIPTS,     // 111 = 7

    // 标识一个区块的数据在本节点的存储状态
    //!< full block available in blk*.dat； 区块数据已存入文件中，给这个块的状态赋值为 BLOCK_HAVE_DATA
    BLOCK_HAVE_DATA = 8,            // 1000
    //!< undo data available in rev*.dat  该区块的undo 数据已存入文件中，给这个块的状态赋值为 BLOCK_HAVE_UNDO
    BLOCK_HAVE_UNDO = 16,           // 10000
    BLOCK_HAVE_MASK = BLOCK_HAVE_DATA | BLOCK_HAVE_UNDO,    //11000 如果一个块的状态等于它，则标识这个块的所有数据，都已经存储在了本节点

    //失败标识
    //!< stage after last reached validness failed； 块的有效性失败
    BLOCK_FAILED_VALID = 32,        // 100000
    //!< descends from failed block  失败区块的后代
    BLOCK_FAILED_CHILD = 64,        // 1000000
    BLOCK_FAILED_MASK = BLOCK_FAILED_VALID | BLOCK_FAILED_CHILD,    //1100000   失败标识，如果块的标识与它相与为真，则标识这个块为无效。
};

/**
 * The block chain is a tree shaped structure starting with the genesis block at
 * the root, with each block potentially having multiple candidates to be the
 * next block. A blockindex may have multiple pprev pointing to it, but at most
 * one of them can be part of the currently active branch.
 */
class CBlockIndex {
public:
    //! pointer to the hash of the block, if any. Memory is owned by this
    //! CBlockIndex
    const uint256 *phashBlock;

    //! pointer to the index of the predecessor of this block
    // 该块的父区块索引
    CBlockIndex *pprev;

    //! pointer to the index of some further predecessor of this block
    // 用来执行跳表的指针。一般指向更早的祖先
    CBlockIndex *pskip;

    //! height of the entry in the chain. The genesis block has height 0
    // 该块索引在主链上的高度。从0开始
    int nHeight;

    //! Which # file this block is stored in (blk?????.dat)
    // 这个块的数据存储的文件号
    int nFile;

    //! Byte offset within blk?????.dat where this block's data is stored
    // 块数据在指定文件中的偏移位置。
    unsigned int nDataPos;

    //! Byte offset within rev?????.dat where this block's undo data is stored
    // 块的undo数据在文件中的偏移位置
    unsigned int nUndoPos;

    //! (memory only) Total amount of work (expected number of hashes) in the
    //! chain up to and including this block
    // 主链上这个块以前的所有工作量；(包括这个块)
    arith_uint256 nChainWork;

    //! Number of transactions in this block.
    //! Note: in a potential headers-first mode, this number cannot be relied
    //! upon
    // 这个块中交易的数量；注意：在只接收到块头模式下，这个状态不能作为依靠。
    unsigned int nTx;

    //! (memory only) Number of transactions in the chain up to and including
    //! this block.
    // 主链上 这个块以前所有的交易数量(包括这个块)
    //! This value will be non-zero only if and only if transactions for this
    //! block and all its parents are available. Change to 64-bit type when
    //! necessary; won't happen before 2030
    // 这个状态的值 只有当这个块以及它所有的父块都可以访问时，才会被设置为非0.  在2030年，
    // 有必要更改到64位。因为整条链上的交易数据量过大，可能会造成数据溢出。
    unsigned int nChainTx;

    //! Verification status of this block. See enum BlockStatus
    // 这个区块的验证状态。注意：一个块的状态时逐层递增的。
    uint32_t nStatus;

    //! block header； 块头的数据
    int32_t nVersion;
    uint256 hashMerkleRoot;
    uint32_t nTime;
    uint32_t nBits;
    uint32_t nNonce;

    //! (memory only) Sequential id assigned to distinguish order in which
    //! blocks are received.  nSequenceId: 被用来区分块的接收顺序
    int32_t nSequenceId;

    //! (memory only) Maximum nTime in the chain upto and including this block.
    //! 主链上，这个区块的最大时间。
    unsigned int nTimeMax;

    void SetNull() {
        phashBlock = nullptr;
        pprev = nullptr;
        pskip = nullptr;
        nHeight = 0;
        nFile = 0;
        nDataPos = 0;
        nUndoPos = 0;
        nChainWork = arith_uint256();
        nTx = 0;
        nChainTx = 0;
        nStatus = 0;
        nSequenceId = 0;
        nTimeMax = 0;

        nVersion = 0;
        hashMerkleRoot = uint256();
        nTime = 0;
        nBits = 0;
        nNonce = 0;
    }

    CBlockIndex() { SetNull(); }

    CBlockIndex(const CBlockHeader &block) {
        SetNull();

        nVersion = block.nVersion;
        hashMerkleRoot = block.hashMerkleRoot;
        nTime = block.nTime;
        nBits = block.nBits;
        nNonce = block.nNonce;
    }

    CDiskBlockPos GetBlockPos() const {
        CDiskBlockPos ret;
        if (nStatus & BLOCK_HAVE_DATA) {
            ret.nFile = nFile;
            ret.nPos = nDataPos;
        }
        return ret;
    }

    CDiskBlockPos GetUndoPos() const {
        CDiskBlockPos ret;
        //如果块索引中有undo数据，就返回undo数据所在的文件位置
        if (nStatus & BLOCK_HAVE_UNDO) {
            ret.nFile = nFile;
            ret.nPos = nUndoPos;
        }
        return ret;
    }

    CBlockHeader GetBlockHeader() const {
        CBlockHeader block;
        block.nVersion = nVersion;
        if (pprev) {
            block.hashPrevBlock = pprev->GetBlockHash();
        }
        block.hashMerkleRoot = hashMerkleRoot;
        block.nTime = nTime;
        block.nBits = nBits;
        block.nNonce = nNonce;
        return block;
    }

    uint256 GetBlockHash() const { return *phashBlock; }

    int64_t GetBlockTime() const { return (int64_t)nTime; }

    int64_t GetBlockTimeMax() const { return (int64_t)nTimeMax; }

    enum { nMedianTimeSpan = 11 };

    int64_t GetMedianTimePast() const {
        int64_t pmedian[nMedianTimeSpan];
        int64_t *pbegin = &pmedian[nMedianTimeSpan];
        int64_t *pend = &pmedian[nMedianTimeSpan];

        const CBlockIndex *pindex = this;
        for (int i = 0; i < nMedianTimeSpan && pindex;
             i++, pindex = pindex->pprev) {
            *(--pbegin) = pindex->GetBlockTime();
        }

        std::sort(pbegin, pend);
        return pbegin[(pend - pbegin) / 2];
    }

    std::string ToString() const {
        return strprintf(
            "CBlockIndex(pprev=%p, nHeight=%d, merkle=%s, hashBlock=%s)", pprev,
            nHeight, hashMerkleRoot.ToString(), GetBlockHash().ToString());
    }

    //! Check whether this block index entry is valid up to the passed validity
    //! level.
    //! 如果当前块的状态 包含传入的验证状态，返回true，否则，返回false。
    bool IsValid(enum BlockStatus nUpTo = BLOCK_VALID_TRANSACTIONS) const {
        // Only validity flags allowed.
        //1. 只允许有效状态传入，此处主要是去除 块数据存储的状态BLOCK_HAVE_DATA，BLOCK_HAVE_UNDO
        assert(!(nUpTo & ~BLOCK_VALID_MASK));

        //2. 如果当前块的索引状态为无效状态，直接返回false，
        if (nStatus & BLOCK_FAILED_MASK) {
            return false;
        }
        //3. 接下来判断该块的状态是否处于 传入的有效状态的之上。如果包含该有效状态，返回true，否则，返回false。
        return ((nStatus & BLOCK_VALID_MASK) >= nUpTo);
    }

    //! Raise the validity level of this block index entry.
    //! Returns true if the validity was changed.
    // 提升块索引的验证等级。如果验证等级被成功修改，返回TRUE。
    // 注意：该状态的设置会清空 块以前的有效状态，只设置当前提升的有效状态。
    bool RaiseValidity(enum BlockStatus nUpTo) {
        // Only validity flags allowed.
        // 只允许有效的标识传递到该方法内。
        // ~BLOCK_VALID_MASK:标识位失败的状态或含有数据的状态; 如果 nUpTo 与取反状态为真，标识传入的标识为 出错标识，此时会断言出错。
        assert(!(nUpTo & ~BLOCK_VALID_MASK));
        //1. 如果传入的提升状态 为出错状态，直接返回false。
        if (nStatus & BLOCK_FAILED_MASK) {
            return false;
        }
        //2. 当前块的有效状态小于 传入的有效状态
        if ((nStatus & BLOCK_VALID_MASK) < nUpTo) {
            // 第一步：(nStatus & ~BLOCK_VALID_MASK)，清空以前的有效验证状态； 第二步：赋值当前提升的有效状态
            nStatus = (nStatus & ~BLOCK_VALID_MASK) | nUpTo;
            return true;
        }
        return false;
    }

    //! Build the skiplist pointer for this entry.
    // 为这个块索引构建跳表
    void BuildSkip();

    //! Efficiently find an ancestor of this block.
    // 高效的查询一个块的祖先。
    CBlockIndex *GetAncestor(int height);
    const CBlockIndex *GetAncestor(int height) const;
};

arith_uint256 GetBlockProof(const CBlockIndex &block);

/**
 * Return the time it would take to redo the work difference between from and
 * to, assuming the current hashrate corresponds to the difficulty at tip, in
 * seconds.
 *
 */
int64_t GetBlockProofEquivalentTime(const CBlockIndex &to,
                                    const CBlockIndex &from,
                                    const CBlockIndex &tip,
                                    const Consensus::Params &);

/** Used to marshal pointers into hashes for db storage. */
class CDiskBlockIndex : public CBlockIndex {
public:
    uint256 hashPrev;

    CDiskBlockIndex() { hashPrev = uint256(); }

    explicit CDiskBlockIndex(const CBlockIndex *pindex) : CBlockIndex(*pindex) {
        hashPrev = (pprev ? pprev->GetBlockHash() : uint256());
    }

    ADD_SERIALIZE_METHODS;

    template <typename Stream, typename Operation>
    inline void SerializationOp(Stream &s, Operation ser_action) {
        int nVersion = s.GetVersion();
        if (!(s.GetType() & SER_GETHASH)) {
            READWRITE(VARINT(nVersion));
        }

        READWRITE(VARINT(nHeight));
        READWRITE(VARINT(nStatus));
        READWRITE(VARINT(nTx));
        if (nStatus & (BLOCK_HAVE_DATA | BLOCK_HAVE_UNDO)) {
            READWRITE(VARINT(nFile));
        }
        if (nStatus & BLOCK_HAVE_DATA) {
            READWRITE(VARINT(nDataPos));
        }
        if (nStatus & BLOCK_HAVE_UNDO) {
            READWRITE(VARINT(nUndoPos));
        }

        // block header
        READWRITE(this->nVersion);
        READWRITE(hashPrev);
        READWRITE(hashMerkleRoot);
        READWRITE(nTime);
        READWRITE(nBits);
        READWRITE(nNonce);
    }

    uint256 GetBlockHash() const {
        CBlockHeader block;
        block.nVersion = nVersion;
        block.hashPrevBlock = hashPrev;
        block.hashMerkleRoot = hashMerkleRoot;
        block.nTime = nTime;
        block.nBits = nBits;
        block.nNonce = nNonce;
        return block.GetHash();
    }

    std::string ToString() const {
        std::string str = "CDiskBlockIndex(";
        str += CBlockIndex::ToString();
        str += strprintf("\n                hashBlock=%s, hashPrev=%s)",
                         GetBlockHash().ToString(), hashPrev.ToString());
        return str;
    }
};

/** An in-memory indexed chain of blocks. */
class CChain {
private:
    std::vector<CBlockIndex *> vChain;

public:
    /**
     * Returns the index entry for the genesis block of this chain, or nullptr
     * if none.
     */
    CBlockIndex *Genesis() const {
        return vChain.size() > 0 ? vChain[0] : nullptr;
    }

    /**
     * Returns the index entry for the tip of this chain, or nullptr if none.
     */
    CBlockIndex *Tip() const {
        return vChain.size() > 0 ? vChain[vChain.size() - 1] : nullptr;
    }

    /**
     * Returns the index entry at a particular height in this chain, or nullptr
     * if no such height exists.
     */
    CBlockIndex *operator[](int nHeight) const {
        if (nHeight < 0 || nHeight >= (int)vChain.size()) {
            return nullptr;
        }
        return vChain[nHeight];
    }

    /** Compare two chains efficiently. */
    friend bool operator==(const CChain &a, const CChain &b) {
        return a.vChain.size() == b.vChain.size() &&
               a.vChain[a.vChain.size() - 1] == b.vChain[b.vChain.size() - 1];
    }

    /** Efficiently check whether a block is present in this chain. */
    bool Contains(const CBlockIndex *pindex) const {
        return (*this)[pindex->nHeight] == pindex;
    }

    /**
     * Find the successor of a block in this chain, or nullptr if the given
     * index is not found or is the tip.
     */
    CBlockIndex *Next(const CBlockIndex *pindex) const {
        if (!Contains(pindex)) {
            return nullptr;
        }

        return (*this)[pindex->nHeight + 1];
    }

    /**
     * Return the maximal height in the chain. Is equal to chain.Tip() ?
     * chain.Tip()->nHeight : -1.
     */
    int Height() const { return vChain.size() - 1; }

    /** Set/initialize a chain with a given tip. */
    void SetTip(CBlockIndex *pindex);

    /**
     * Return a CBlockLocator that refers to a block in this chain (by default
     * the tip).
     */
    CBlockLocator GetLocator(const CBlockIndex *pindex = nullptr) const;

    /**
     * Find the last common block between this chain and a block index entry.
     */
    const CBlockIndex *FindFork(const CBlockIndex *pindex) const;

    /**
     * Find the earliest block with timestamp equal or greater than the given.
     */
    CBlockIndex *FindEarliestAtLeast(int64_t nTime) const;
};

#endif // BITCOIN_CHAIN_H
