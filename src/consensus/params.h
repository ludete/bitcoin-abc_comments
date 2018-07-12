// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CONSENSUS_PARAMS_H
#define BITCOIN_CONSENSUS_PARAMS_H

#include "uint256.h"

#include <map>
#include <string>

namespace Consensus {

enum DeploymentPos {
    DEPLOYMENT_TESTDUMMY,
    // Deployment of BIP68, BIP112, and BIP113.
    DEPLOYMENT_CSV,
    // NOTE: Also add new deployments to VersionBitsDeploymentInfo in
    // versionbits.cpp
    MAX_VERSION_BITS_DEPLOYMENTS
};

/**
 * Struct for each individual consensus rule change using BIP9.
 */
struct BIP9Deployment {
    /** Bit position to select the particular bit in nVersion. */
    int bit;
    /** Start MedianTime for version bits miner confirmation. Can be a date in
     * the past */
    int64_t nStartTime;
    /** Timeout/expiry MedianTime for the deployment attempt. */
    int64_t nTimeout;
};

/**
 * Parameters that influence chain consensus.
 */
struct Params {
    uint256 hashGenesisBlock;//创世区块的hash
    int nSubsidyHalvingInterval;//奖励减半时间间隔
    /** Block height and hash at which BIP34 becomes active */
    int BIP34Height;//区块高度
    uint256 BIP34Hash;//区块hash
    /** Block height at which BIP65 becomes active */
    int BIP65Height;
    /** Block height at which BIP66 becomes active */
    int BIP66Height;
    /** Block height at which UAHF kicks in */
    int uahfHeight;
    /** Block height at which OP_RETURN replay protection stops */
    int antiReplayOpReturnSunsetHeight;
    /** Committed OP_RETURN value for replay protection */
    std::vector<uint8_t> antiReplayOpReturnCommitment;
    /**
     * Minimum blocks including miner confirmation of the total of 2016 blocks
     * in a retargeting period, (nPowTargetTimespan / nPowTargetSpacing) which
     * is also used for BIP9 deployments.
     * Examples: 1916 for 95%, 1512 for testchains.
     * 在2016个区块中至少要有多少个区块被矿工确认，规则改变才能生效
     * 在BIP9上线时还使用(nPowTargetTimespan / nPowTargetSpacing)值
     */
    uint32_t nRuleChangeActivationThreshold;
    uint32_t nMinerConfirmationWindow;
    BIP9Deployment vDeployments[MAX_VERSION_BITS_DEPLOYMENTS];
    /** Proof of work parameters */
    uint256 powLimit;//难度
    bool fPowAllowMinDifficultyBlocks;//是否允许最低难度
    bool fPowNoRetargeting;//不调整难度
    int64_t nPowTargetSpacing;//区块产生平均时间
    int64_t nPowTargetTimespan;//难度调整时间
    int64_t DifficultyAdjustmentInterval() const {
        return nPowTargetTimespan / nPowTargetSpacing;
    }
    uint256 nMinimumChainWork;//当前难度最小值
    uint256 defaultAssumeValid;//在此之前的区块都认为是有效的

    /** Activation time at which the cash HF kicks in. */
    int64_t cashHardForkActivationTime;
};
} // namespace Consensus

#endif // BITCOIN_CONSENSUS_PARAMS_H
