// Copyright (c) 2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CONSENSUS_VERSIONBITS
#define BITCOIN_CONSENSUS_VERSIONBITS

#include "chain.h"
#include <map>

/** What block version to use for new blocks (pre versionbits) */
static const int32_t VERSIONBITS_LAST_OLD_BLOCK_VERSION = 4;
/** What bits to set in version for versionbits blocks */
static const int32_t VERSIONBITS_TOP_BITS = 0x20000000UL;
/** What bitmask determines whether versionbits is in use */
static const int32_t VERSIONBITS_TOP_MASK = 0xE0000000UL;
/** Total bits available for versionbits */
static const int32_t VERSIONBITS_NUM_BITS = 29;

enum ThresholdState {
    THRESHOLD_DEFINED,
    THRESHOLD_STARTED,
    THRESHOLD_LOCKED_IN,
    THRESHOLD_ACTIVE,
    THRESHOLD_FAILED,
};

// A map that gives the state for blocks whose height is a multiple of Period().
// The map is indexed by the block's parent, however, so all keys in the map
// will either be nullptr or a block with (height + 1) % Period() == 0.
//一个map缓存某个高度的块的状态在某个区间。这个map以该区块的父区块作为索引，所以，该map中的所有key
// 将是null或者(height+1) % Period() == 0 的区块
typedef std::map<const CBlockIndex *, ThresholdState> ThresholdConditionCache;

struct BIP9DeploymentInfo {
    /** Deployment name */
    const char *name;
    /** Whether GBT clients can safely ignore this rule in simplified usage
     * 是否客户端可以安全的忽略这个部署
     * */
    bool gbt_force;
};

extern const struct BIP9DeploymentInfo VersionBitsDeploymentInfo[];

/**
 * Abstract class that implements BIP9-style threshold logic, and caches
 * results.  抽象类，实现BIP9的阈值逻辑，缓存获取的结果
 */
class AbstractThresholdConditionChecker {
protected:
    virtual bool Condition(const CBlockIndex *pindex,
                           const Consensus::Params &params) const = 0;
    virtual int64_t BeginTime(const Consensus::Params &params) const = 0;
    virtual int64_t EndTime(const Consensus::Params &params) const = 0;
    virtual int Period(const Consensus::Params &params) const = 0;
    virtual int Threshold(const Consensus::Params &params) const = 0;

public:
    // Note that the functions below take a pindexPrev as input: they compute
    // information for block B based on its parent.
    //注意：这个函数依赖于当前区块的父区块来计算该区块的信息。
    ThresholdState GetStateFor(const CBlockIndex *pindexPrev,
                               const Consensus::Params &params,
                               ThresholdConditionCache &cache) const;
    int GetStateSinceHeightFor(const CBlockIndex *pindexPrev,
                               const Consensus::Params &params,
                               ThresholdConditionCache &cache) const;
};

//内部元素为一个map数组，
struct VersionBitsCache {
    ThresholdConditionCache caches[Consensus::MAX_VERSION_BITS_DEPLOYMENTS];

    void Clear();
};

ThresholdState VersionBitsState(const CBlockIndex *pindexPrev,
                                const Consensus::Params &params,
                                Consensus::DeploymentPos pos,
                                VersionBitsCache &cache);
int VersionBitsStateSinceHeight(const CBlockIndex *pindexPrev,
                                const Consensus::Params &params,
                                Consensus::DeploymentPos pos,
                                VersionBitsCache &cache);
uint32_t VersionBitsMask(const Consensus::Params &params,
                         Consensus::DeploymentPos pos);

#endif
