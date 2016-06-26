/**
 * @brief threadsafequeue.hh
 *
 * @date  : Jun 21, 2016
 * @author: lpzun
 */

#ifndef THREADSAFEQUEUE_HH_
#define THREADSAFEQUEUE_HH_

#include <iostream>
#include <deque>
#include <queue>
#include <string>
#include <thread>
#include <mutex>
#include <atomic>

using std::cout;
using std::cin;
using std::cerr;
using std::endl;

using std::deque;
using std::queue;
using std::thread;
using std::string;
using std::mutex;
using std::condition_variable;
using std::lock_guard;
using std::unique_lock;
using std::shared_ptr;

namespace bssp {
/// File: Thread Safe data structure queue
///
template<typename T> class threadsafe_queue {
public:
    threadsafe_queue() :
            mtx(), cond(), worklist() {
    }

    ~threadsafe_queue() {
    }

    threadsafe_queue(const threadsafe_queue&) = delete;
    threadsafe_queue &operator=(const threadsafe_queue&) = delete;

    void push(const T& _value) {
        shared_ptr<T> pv(std::make_shared<T>(std::move(_value)));
        lock_guard<mutex> lck(mtx);
        worklist.emplace_back(pv);
        cond.notify_all();
    }

    void pop(T& _value) {
        unique_lock<mutex> lck(mtx);
        cond.wait(lck, [this] {return !worklist.empty();});
        _value = std::move(*worklist.front());
        worklist.pop_front();
    }

    std::shared_ptr<T> pop() {
        unique_lock<mutex> lck(mtx);
        cond.wait(lck, [this] {return !worklist.empty();});
        shared_ptr<T> res = worklist.front();
        worklist.pop_front();
        return res;
    }

    bool try_pop(T& _value) {
        lock_guard<mutex> lck(mtx);
        if (worklist.empty())
            return false;
        _value = std::move(*worklist.front());
        worklist.pop_front();
        return true;
    }

    std::shared_ptr<T> try_pop() {
        lock_guard<mutex> lck(mtx);
        if (worklist.empty())
            return std::shared_ptr<T>();
        shared_ptr<T> res = worklist.front();
        worklist.pop_front();
        return res;
    }

    bool empty() const {
        lock_guard<mutex> lck(mtx);
        return worklist.empty();
    }

    size_t size() const {
        lock_guard<mutex> lck(mtx);
        return worklist.size();
    }

    template<typename Predicate>
    bool minimal(Predicate pred) {
        lock_guard<mutex> lck(mtx);
        auto iw = worklist.begin();
        while (iw != worklist.end()) {
            if (pred(*iw))
                return false;
            ++iw;
        }
        return true;
    }

    template<typename Predicate>
    void minimize(Predicate pred) {
        lock_guard<mutex> lck(mtx);
        auto iw = worklist.begin();
        while (iw != worklist.end()) {
            if (pred(*iw))
                iw = worklist.erase(iw);
            else
                ++iw;
        }
    }

    template<typename Predicate>
    void minimize(const T& _value, Predicate pred) {
        shared_ptr<T> pv(std::make_shared<T>(std::move(_value)));
        lock_guard<mutex> lck(mtx);
        auto iw = worklist.begin();
        while (iw != worklist.end()) {
            if (pred(*iw))
                iw = worklist.erase(iw);
            else
                ++iw;
        }
        worklist.emplace_back(pv);
        cond.notify_all();
    }

private:
    mutable mutex mtx;
    condition_variable cond;
    deque<shared_ptr<T>> worklist;

};

} /* namespace ucob */

#endif /* THREADSAFEQUEUE_HH_ */
