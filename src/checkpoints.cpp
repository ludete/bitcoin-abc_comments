// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "checkpoints.h"

#include "chain.h"
#include "chainparams.h"
#include "uint256.h"
#include "validation.h"

#include <cstdint>

#include <boost/range/adaptor/reversed.hpp>

namespace Checkpoints {

// 获取配置参数中一个检查点;
CBlockIndex *GetLastCheckpoint(const CCheckpointData &data) {
    const MapCheckpoints &checkpoints = data.mapCheckpoints;

    // 从后往前(从高块向低块)，查找检查点，当一个检查点在全局状态中找到时，就将它的块索引返回
    for (const MapCheckpoints::value_type &i :
         boost::adaptors::reverse(checkpoints)) {
        const uint256 &hash = i.second;
        BlockMap::const_iterator t = mapBlockIndex.find(hash);
        if (t != mapBlockIndex.end()) return t->second;
    }
    return nullptr;
}

} // namespace Checkpoints
