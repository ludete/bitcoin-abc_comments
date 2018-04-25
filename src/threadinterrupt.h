// Copyright (c) 2016 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_THREADINTERRUPT_H
#define BITCOIN_THREADINTERRUPT_H

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <mutex>

/**
 * A helper class for interruptible sleeps. Calling operator() will interrupt
 * any current sleep, and after that point operator bool() will return true
 * until reset.
 * 一个辅助类，去中断睡眠。调用重载的()操作符，将打断任何当前的休眠。并且在这个打断点之后，
 * 操作重载的bool运算符，返回是否被设置
 */
class CThreadInterrupt {
public:
    explicit operator bool() const;
    // 通过内部的条件变量，唤醒所有的睡眠线程；
    void operator()();
    void reset();
    bool sleep_for(std::chrono::milliseconds rel_time);
    bool sleep_for(std::chrono::seconds rel_time);
    bool sleep_for(std::chrono::minutes rel_time);

private:
    std::condition_variable cond;
    std::mutex mut;
    std::atomic<bool> flag;
};

#endif // BITCOIN_THREADINTERRUPT_H
