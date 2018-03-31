// Copyright (c) 2012-2015 The Bitcoin Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#ifndef BITCOIN_CHECKQUEUE_H
#define BITCOIN_CHECKQUEUE_H

#include <algorithm>
#include <vector>

#include <boost/thread/condition_variable.hpp>
#include <boost/thread/locks.hpp>
#include <boost/thread/mutex.hpp>

template <typename T> class CCheckQueueControl;

/**
 * Queue for verifications that have to be performed.
 * The verifications are represented by a type T, which must provide an
 * operator(), returning a bool.
 *
 * One thread (the master) is assumed to push batches of verifications onto the
 * queue, where they are processed by N-1 worker threads. When the master is
 * done adding work, it temporarily joins the worker pool as an N'th worker,
 * until all jobs are done.
 */
template <typename T> class CCheckQueue {
private:
    //! Mutex to protect the inner state
    // 互斥锁保护内部的状态
    boost::mutex mutex;

    //! Worker threads block on this when out of work
    // 在没有工作时，工作线程阻塞条件变量。
    boost::condition_variable condWorker;

    //! Master thread blocks on this when out of work
    // 在没有工作时，master线程阻塞条件变量。
    boost::condition_variable condMaster;

    //! The queue of elements to be processed.
    //! As the order of booleans doesn't matter, it is used as a LIFO (stack)
    // 要处理元素的队列。因为bool值的队列并不重要，它被用来作为一个LIFO(队列)
    std::vector<T> queue;

    //! The number of workers (including the master) that are idle.
    // 空闲的工作线程数量(包含主线程)
    int nIdle;

    //! The total number of workers (including the master).
    // 总的工作线程的数量，包含主线程
    int nTotal;

    //! The temporary evaluation result.
    // 临时评估结果
    bool fAllOk;

    /**
     * Number of verifications that haven't completed yet.
     * This includes elements that are no longer queued, but still in the
     * worker's own batches.
     */
    // 至今还有多少验证任务没有完成。包括不再排队，但仍在工作线程自己的批次中的任务数量。
    unsigned int nTodo;

    //! Whether we're shutting down.
    // 是否需要退出。
    bool fQuit;

    //! The maximum number of elements to be processed in one batch
    // 每个批次最大的元素处理数量
    unsigned int nBatchSize;

    /** Internal function that does bulk of the verification work.
     * 内部函数，做大量的脚本验证； 对象去调用大量的方法
     * */
    bool Loop(bool fMaster = false) {
        // 根据参数，选择条件变量，更换不同的线程
        boost::condition_variable &cond = fMaster ? condMaster : condWorker;

        std::vector<T> vChecks;     //临时任务队列
        vChecks.reserve(nBatchSize);
        unsigned int nNow = 0;      //该值为每个线程内的局部变量
        bool fOk = true;
        do {
            {
                boost::unique_lock<boost::mutex> lock(mutex);       //启动RAII机制，自动管理资源锁；
                // first do the clean-up of the previous loop run (allowing us
                // to do it in the same critsect)  首先做清理前的一次循环运行。 允许在相同的共识下去运行它。
                if (nNow) {
                    fAllOk &= fOk;
                    nTodo -= nNow;
                    if (nTodo == 0 && !fMaster)
                        // We processed the last element; inform the master it
                        // can exit and return the result  处理最后一个元素，通知master它可以退出，并且返回结果
                        condMaster.notify_one();
                } else {

                    // nNow == 0,标识该线程第一次运行，即工作线程的数量又增加了一个。
                    // first iteration  第一次迭代；每次loop都标识增加了一个线程。
                    nTotal++;
                }
                // logically, the do loop starts here。 逻辑上，任务循环从这里开始。
                // 该对象的任务队列外空时，进入下列条件；
                // 下面处理分为两种情况：1. 任务全部完成后，将主线程退出。
                //  2. 任务全部完成后，将子线程
                while (queue.empty()) {
                    // 当验证任务为0，且需要退出时，
                    if ((fMaster || fQuit) && nTodo == 0) {
                        nTotal--;
                        bool fRet = fAllOk;     //fAllOk : 最新的临时评估结果。对该值做缓存，然后退出。
                        // reset the status for new work later
                        if (fMaster) fAllOk = true;
                        // return the current status        //返回当前的状态。
                        return fRet;
                    }
                    nIdle++;
                    cond.wait(lock); // wait   此处配合条件变量使用。进行线程间的同步;此处释放锁。
                    nIdle--;
                }
                // Decide how many work units to process now.
                // * Do not try to do everything at once, but aim for
                // increasingly smaller batches so all workers finish
                // approximately simultaneously.
                // * Try to account for idle jobs which will instantly start
                // helping.
                // * Don't do batches smaller than 1 (duh), or larger than
                // nBatchSize.
                // 决定现在处理多少个工作单元。
                // 不要尝试一次处理所有的事情，而是争取采用更小的工作批次，以便所有的
                // 工作线程几乎同时完成手上的工作。
                // 获取当前每个线程处理的任务数量
                nNow = std::max(
                    1U, std::min(nBatchSize, (unsigned int)queue.size() /
                                                 (nTotal + nIdle + 1)));
                //从类的任务队列中 向临时队列中添加任务。
                vChecks.resize(nNow);
                for (unsigned int i = 0; i < nNow; i++) {
                    // We want the lock on the mutex to be as short as possible,
                    // so swap jobs from the global queue to the local batch
                    // vector instead of copying.
                    // 想让锁的时间尽可能的短，所以采用这种方法(move)来从 类的队列中拿到任务，而不是采用拷贝的方式。
                    vChecks[i].swap(queue.back());
                    queue.pop_back();       //将放到局部队列中的任务清除
                }
                // Check whether we need to do work at all
                // 查看是否需要完成工作。
                fOk = fAllOk;
            }
            // execute work； 执行本线程刚分到的工作。
            for (T &check : vChecks) {
                if (fOk) fOk = check();
            }
            // 执行完后，清空临时任务的集合。继续下次循环。
            vChecks.clear();
        } while (true);
    }

public:
    //! Create a new check queue
    CCheckQueue(unsigned int nBatchSizeIn)
            : nIdle(0), nTotal(0), fAllOk(true), nTodo(0), fQuit(false),
              nBatchSize(nBatchSizeIn) {}

    //! Worker thread
    void Thread() { Loop(); }

    //! Wait until execution finishes, and return whether all evaluations were
    //! successful.
    //! 等待执行完成所有的任务后，线程退出
    bool Wait() { return Loop(true); }

    //! Add a batch of checks to the queue
    //! 给类的内部队列添加一批检查任务；该队列受所保护，以及内部元素受锁保护。
    void Add(std::vector<T> &vChecks) {
        boost::unique_lock<boost::mutex> lock(mutex);
        //将任务添加至 内部队列中
        for (T &check : vChecks) {
            queue.push_back(std::move(check));
        }
        // 更新未完成的任务数量
        nTodo += vChecks.size();
        //如果刚添加的任务数量为1，只唤醒一个线程去处理；否则，唤醒全部线程
        if (vChecks.size() == 1) {
            condWorker.notify_one();
        } else if (vChecks.size() > 1) {
            condWorker.notify_all();
        }
    }

    ~CCheckQueue() {}

    // 是否处于休眠状态
    bool IsIdle() {
        boost::unique_lock<boost::mutex> lock(mutex);
        return (nTotal == nIdle && nTodo == 0 && fAllOk == true);
    }
};

/**
 * RAII-style controller object for a CCheckQueue that guarantees the passed
 * queue is finished before continuing.
 * RAII类型的 控制器，控制CCheckQueue 对象，保证队列下次运行时，任务已经完成。
 */

// 这个类的运行方法：1. 先用一个CCheckQueue 对象构建一个该类的对象。
//      2. 调用该类的添加方法， 向CCheckQueue 中添加任务；
//      3. 在该类析构时，处理 CCheckQueue 中现存的所有任务，完成后，CCheckQueue 本身的线程休眠，主线程退出。该类析构完毕。
template <typename T> class CCheckQueueControl {
private:
    CCheckQueue<T> *pqueue;
    bool fDone;

public:
    CCheckQueueControl(CCheckQueue<T> *pqueueIn)
        : pqueue(pqueueIn), fDone(false) {
        // passed queue is supposed to be unused, or nullptr
        // 传递的队列应当是未使用的，或者为空
        if (pqueue != nullptr) {
            bool isIdle = pqueue->IsIdle();     //获取该队列是否空闲
            assert(isIdle);
        }
    }

    bool Wait() {
        if (pqueue == nullptr) return true;
        bool fRet = pqueue->Wait();     //执行完所有的任务后，
        fDone = true;
        return fRet;
    }

    // 向 CCheckQueue 中添加任务；
    void Add(std::vector<T> &vChecks) {
        if (pqueue != nullptr) pqueue->Add(vChecks);
    }

    // 该对象析构时，检查队列(CCheckQueue)中的所有任务都已被处理，此时所有的线程都处于休眠状态。
    ~CCheckQueueControl() {
        if (!fDone) Wait();
    }
};

#endif // BITCOIN_CHECKQUEUE_H
