// Copyright (c) 2017 The Bitcoin developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "scriptcache.h"

#include "crypto/sha256.h"
#include "cuckoocache.h"
#include "primitives/transaction.h"
#include "random.h"
#include "script/sigcache.h"
#include "sync.h"
#include "util.h"
#include "validation.h"

static CuckooCache::cache<uint256, SignatureCacheHasher> scriptExecutionCache;

//全局的静态变量；每次客户端启动，都算一次，然后对本次启动所有检查过的交易做标记。
static uint256 scriptExecutionCacheNonce(GetRandHash());

void InitScriptExecutionCache() {
    // nMaxCacheSize is unsigned. If -maxscriptcachesize is set to zero,
    // setup_bytes creates the minimum possible cache (2 elements).
    size_t nMaxCacheSize =
        std::min(std::max(int64_t(0), GetArg("-maxscriptcachesize",
                                             DEFAULT_MAX_SCRIPT_CACHE_SIZE)),
                 MAX_MAX_SCRIPT_CACHE_SIZE) *
        (size_t(1) << 20);
    size_t nElems = scriptExecutionCache.setup_bytes(nMaxCacheSize);
    LogPrintf("Using %zu MiB out of %zu requested for script execution cache, "
              "able to store %zu elements\n",
              (nElems * sizeof(uint256)) >> 20, nMaxCacheSize >> 20, nElems);
}

//获取交易哈希的缓存key，这样当第一次检查完交易后，就将该交易写入缓存中，当下次再收到该交易时，就不再检查该交易了。
uint256 GetScriptCacheKey(const CTransaction &tx, uint32_t flags) {
    uint256 key;
    // We only use the first 19 bytes of nonce to avoid a second SHA round -
    // giving us 19 + 32 + 4 = 55 bytes (+ 8 + 1 = 64)
    // 只使用 nonce的前19个字节
    static_assert(55 - sizeof(flags) - 32 >= 128 / 8,
                  "Want at least 128 bits of nonce for script execution cache");
    CSHA256()
        .Write(scriptExecutionCacheNonce.begin(), 55 - sizeof(flags) - 32)
        .Write(tx.GetHash().begin(), 32)
        .Write((uint8_t *)&flags, sizeof(flags))
        .Finalize(key.begin());
    // 一次写入 本次开机随机哈希的前19个字节， 该交易的哈希，以及检测该交易时的标识，用上述这些数据来计算该交易的缓存哈希。

    return key;
}

bool IsKeyInScriptCache(uint256 key, bool erase) {
    // TODO: Remove this requirement by making CuckooCache not require external
    // locks
    AssertLockHeld(cs_main);
    return scriptExecutionCache.contains(key, erase);
}

void AddKeyInScriptCache(uint256 key) {
    // TODO: Remove this requirement by making CuckooCache not require external
    // locks
    AssertLockHeld(cs_main);
    scriptExecutionCache.insert(key);
}
