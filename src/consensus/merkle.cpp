// Copyright (c) 2015-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "merkle.h"
#include "hash.h"
#include "utilstrencodings.h"

/*     WARNING! If you're reading this because you're learning about crypto
       and/or designing a new system that will use merkle trees, keep in mind
       that the following merkle tree algorithm has a serious flaw related to
       duplicate txids, resulting in a vulnerability (CVE-2012-2459).
       如果你正在读本文，可能是正在学习或者准备使用merkle tree 构建一个新系统，记住：
       下面的merkle tree算法对重读的txid有一个严重的缺陷，从而导致了漏洞。

       The reason is that if the number of hashes in the list at a given time
       is odd, the last one is duplicated before computing the next level (which
       is unusual in Merkle trees). This results in certain sequences of
       transactions leading to the same merkle root. For example, these two
       trees:
       原因是如果在给定的列表中哈希个数是奇数，那么在计算下一个级别（这在Merkle树中是不寻常的）
       之前，最后一个是重复的。 这导致某些事务序列导致相同的merkle根。 例如，这两棵树
                    A               A
                  /  \            /   \
                B     C         B       C
               / \    |        / \     / \
              D   E   F       D   E   F   F
             / \ / \ / \     / \ / \ / \ / \
             1 2 3 4 5 6     1 2 3 4 5 6 5 6

       for transaction lists [1,2,3,4,5,6] and [1,2,3,4,5,6,5,6] (where 5 and
       6 are repeated) result in the same root hash A (because the hash of both
       of (F) and (F,F) is C).

       The vulnerability results from being able to send a block with such a
       transaction list, with the same merkle root, and the same block hash as
       the original without duplication, resulting in failed validation. If the
       receiving node proceeds to mark that block as permanently invalid
       however, it will fail to accept further unmodified (and thus potentially
       valid) versions of the same block.
       We defend against this by detecting
       the case where we would hash two identical hashes at the end of the list
       together, and treating that identically to the block having an invalid
       merkle root. Assuming no double-SHA256 collisions, this will detect all
       known ways of changing the transactions without affecting the merkle
       root.
       这个漏洞导致可以发送 一个含有这样交易列表的块，与原始的没有重复交易的块 含有相同的
       merkle Root, 相同的块哈希，但是这个块将会由于重复的交易验证失败。如果接收节点此时去标记
       这个哈希所代表的块为无效，那么当正确的原始块来的时候，它就不会再被这个节点接收。
       通过检测将两个相同的哈希散列在列表末尾的情况 来防止发生上述攻击，并将包含这种攻击的块与包
       含无效merkle Root的块视为一样。假设没有sha256冲突，此处将会检测所有已知修改交易的方式
       但并不会影响merkle root.

*/

/* This implements a constant-space merkle root/path calculator, limited to 2^32
 * leaves.
 * 实现了一个恒定空间的 merkle路径计算，限制叶子节点为2**32个。
 *
 * 当直接计算一个块的哈希时，参数：branchpos = -1； pbranch = nil.
 * */
static void MerkleComputation(const std::vector<uint256> &leaves,
                              uint256 *proot, bool *pmutated,
                              uint32_t branchpos,
                              std::vector<uint256> *pbranch) {

    //Note： 下面的注释都是处在 直接生成一个块的merkle Root的逻辑上推导的。

    if (pbranch) pbranch->clear();
    // 1. 检查传入叶子个数，如果为0，赋值错误pmutated=false，然后退回。
    if (leaves.size() == 0) {
        if (pmutated) *pmutated = false;
        if (proot) *proot = uint256();
        return;
    }
    bool mutated = false;
    // count is the number of leaves processed so far.
    //2. count 是目前为止叶子的处理的叶子数量
    uint32_t count = 0;
    // inner is an array of eagerly computed subtree hashes, indexed by tree
    // level (0 being the leaves).
    // inner 是一个计算后的哈希子树的数组，通过树的level 作为索引。
    // For example, when count is 25 (11001 in binary), inner[4] is the hash of
    // the first 16 leaves, inner[3] of the next 8 leaves, and inner[0] equal to
    // the last leaf. The other inner entries are undefined.
    // 例如：当count=25(即处理的叶子数目为25)，inner[4]是前16个
    uint256 inner[32];
    // Which position in inner is a hash that depends on the matching leaf.
    // inner位置的某个元素是一个依赖于匹配叶子的哈希。
    int matchlevel = -1;
    // First process all leaves into 'inner' values.
    //3. 首先处理所有的叶子，然后写入inner中。
    while (count < leaves.size()) {
        uint256 h = leaves[count];
        bool matchh = count == branchpos;
        count++;        //累计处理的叶子数目
        int level;
        // For each of the lower bits in count that are 0, do 1 step. Each
        // corresponds to an inner value that existed before processing the
        // current leaf, and each needs a hash to combine it.
        // 在计数为0的每个较低位，执行1步。对应于处理当前叶子之前存在的每个inner的值，
        // 都需要一个哈希来标识。
        for (level = 0; !(count & (((uint32_t)1) << level)); level++) {
            if (pbranch) {
                if (matchh) {
                    pbranch->push_back(inner[level]);
                } else if (matchlevel == level) {
                    pbranch->push_back(h);
                    matchh = true;
                }
            }
            mutated |= (inner[level] == h);
            CHash256()
                .Write(inner[level].begin(), 32)
                .Write(h.begin(), 32)
                .Finalize(h.begin());
        }
        // Store the resulting hash at inner position level.
        // 在inner的位置层级存储哈希
        inner[level] = h;
        if (matchh) {
            matchlevel = level;
        }
    }

    //4. 进行下一步的处理
    // Do a final 'sweep' over the rightmost branch of the tree to process
    // odd levels, and reduce everything to a single top value.
    // Level is the level (counted from the bottom) up to which we've sweeped.
    int level = 0;
    // As long as bit number level in count is zero, skip it. It means there
    // is nothing left at this level.
    while (!(count & (((uint32_t)1) << level))) {
        level++;
    }
    uint256 h = inner[level];
    bool matchh = matchlevel == level;
    while (count != (((uint32_t)1) << level)) {
        // If we reach this point, h is an inner value that is not the top.
        // We combine it with itself (Bitcoin's special rule for odd levels in
        // the tree) to produce a higher level one.
        if (pbranch && matchh) {
            pbranch->push_back(h);
        }
        CHash256()
            .Write(h.begin(), 32)
            .Write(h.begin(), 32)
            .Finalize(h.begin());
        // Increment count to the value it would have if two entries at this
        // level had existed.
        count += (((uint32_t)1) << level);
        level++;
        // And propagate the result upwards accordingly.
        while (!(count & (((uint32_t)1) << level))) {
            if (pbranch) {
                if (matchh) {
                    pbranch->push_back(inner[level]);
                } else if (matchlevel == level) {
                    pbranch->push_back(h);
                    matchh = true;
                }
            }
            CHash256()
                .Write(inner[level].begin(), 32)
                .Write(h.begin(), 32)
                .Finalize(h.begin());
            level++;
        }
    }
    // Return result.
    if (pmutated) *pmutated = mutated;
    if (proot) *proot = h;
}

//生成 merkle树
uint256 ComputeMerkleRoot(const std::vector<uint256> &leaves, bool *mutated) {
    uint256 hash;
    MerkleComputation(leaves, &hash, mutated, -1, nullptr);
    return hash;
}

std::vector<uint256> ComputeMerkleBranch(const std::vector<uint256> &leaves,
                                         uint32_t position) {
    std::vector<uint256> ret;
    MerkleComputation(leaves, nullptr, nullptr, position, &ret);
    return ret;
}

uint256 ComputeMerkleRootFromBranch(const uint256 &leaf,
                                    const std::vector<uint256> &vMerkleBranch,
                                    uint32_t nIndex) {
    uint256 hash = leaf;
    for (std::vector<uint256>::const_iterator it = vMerkleBranch.begin();
         it != vMerkleBranch.end(); ++it) {
        if (nIndex & 1) {
            hash = Hash(BEGIN(*it), END(*it), BEGIN(hash), END(hash));
        } else {
            hash = Hash(BEGIN(hash), END(hash), BEGIN(*it), END(*it));
        }
        nIndex >>= 1;
    }
    return hash;
}

//生成一个块的merkle树。
uint256 BlockMerkleRoot(const CBlock &block, bool *mutated) {
    std::vector<uint256> leaves;
    //1. 计算块中每个交易的哈希
    leaves.resize(block.vtx.size());
    for (size_t s = 0; s < block.vtx.size(); s++) {
        leaves[s] = block.vtx[s]->GetId();
    }
    //2. 依据这些交易哈希生成merkle树
    return ComputeMerkleRoot(leaves, mutated);
}

std::vector<uint256> BlockMerkleBranch(const CBlock &block, uint32_t position) {
    std::vector<uint256> leaves;
    leaves.resize(block.vtx.size());
    for (size_t s = 0; s < block.vtx.size(); s++) {
        leaves[s] = block.vtx[s]->GetId();
    }
    return ComputeMerkleBranch(leaves, position);
}
