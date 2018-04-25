// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "threadinterrupt.h"

//加载flag中的数据。
CThreadInterrupt::operator bool() const {
    return flag.load(std::memory_order_acquire);
}

//重新设置flag
void CThreadInterrupt::reset() {
    flag.store(false, std::memory_order_release);
}

//打断所有的睡眠线程。ß
void CThreadInterrupt::operator()() {
    {
        std::unique_lock<std::mutex> lock(mut);
        flag.store(true, std::memory_order_release);
    }
    cond.notify_all();
}

//睡眠一定的时间
bool CThreadInterrupt::sleep_for(std::chrono::milliseconds rel_time) {
    std::unique_lock<std::mutex> lock(mut);
    return !cond.wait_for(lock, rel_time, [this]() {
        return flag.load(std::memory_order_acquire);
    });
}

bool CThreadInterrupt::sleep_for(std::chrono::seconds rel_time) {
    return sleep_for(
        std::chrono::duration_cast<std::chrono::milliseconds>(rel_time));
}

bool CThreadInterrupt::sleep_for(std::chrono::minutes rel_time) {
    return sleep_for(
        std::chrono::duration_cast<std::chrono::milliseconds>(rel_time));
}
