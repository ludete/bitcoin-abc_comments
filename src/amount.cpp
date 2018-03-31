// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "amount.h"

#include "tinyformat.h"

const std::string CURRENCY_UNIT = "BCC";

std::string Amount::ToString() const {
    return strprintf("%d.%08d %s", amount / COIN.GetSatoshis(),
                     amount % COIN.GetSatoshis(), CURRENCY_UNIT);
}

// nFeePaid(in): nBytes_个字节的总交易费； nBytes_(in):总的字节个数；
CFeeRate::CFeeRate(const Amount nFeePaid, size_t nBytes_) {
    assert(nBytes_ <= uint64_t(std::numeric_limits<int64_t>::max()));
    int64_t nSize = int64_t(nBytes_);

    if (nSize > 0) {
        nSatoshisPerK = 1000 * nFeePaid / nSize;        //计算当前每千字节的交易费
    } else {
        nSatoshisPerK = 0;
    }
}

//返回该字节总的交易费
Amount CFeeRate::GetFee(size_t nBytes_) const {
    assert(nBytes_ <= uint64_t(std::numeric_limits<int64_t>::max()));
    int64_t nSize = int64_t(nBytes_);

    Amount nFee = nSize * nSatoshisPerK / 1000;     //返回该字节总的交易费

    if (nFee == 0 && nSize != 0) {
        if (nSatoshisPerK > 0) {
            nFee = Amount(1);               //如果千字节费率大于0，则返回 这些字节总的费为1.
        }
        if (nSatoshisPerK < 0) {
            nFee = Amount(-1);
        }
    }

    return nFee;
}

std::string CFeeRate::ToString() const {
    return strprintf(
        "%d.%08d %s/kB", nSatoshisPerK.GetSatoshis() / COIN.GetSatoshis(),
        nSatoshisPerK.GetSatoshis() % COIN.GetSatoshis(), CURRENCY_UNIT);
}
