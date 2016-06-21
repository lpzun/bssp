/**
 * @name state.hh
 *
 * @date  : Jun 21, 2015
 * @author: Peizun Liu
 */

#ifndef STATE_HH_
#define STATE_HH_

#include "algs.hh"

namespace bssp {

/// define local state
using local_state = unsigned short;

/// define the size of local states
using size_l = unsigned short;

/// define shared state
using shared_state = unsigned short;

/// define size of shared states
using size_s = unsigned short;

/// define the counter of thread state
using size_p = unsigned short;

/// define the thread_state id
using id_thread_state = unsigned int;

/// define the transition id
using id_transition = unsigned int;

/// class thread state
class thread_state {
public:
    static size_s S; /// the size of shared state
    static size_l L; /// the size of local  state

    inline thread_state();
    inline thread_state(const thread_state& t);
    inline thread_state(const shared_state& share, const local_state& local);
    ~thread_state() {
    }

    ostream& to_stream(ostream& out = cout) const;

    inline local_state get_local() const {
        return local;
    }

    inline shared_state get_share() const {
        return share;
    }

private:
    shared_state share;
    local_state local;
};

/**
 * @brief default constructor
 */
inline thread_state::thread_state() :
        share(0), local(0) {
}

/**
 * @brief constructor with thread state
 * @param t
 */
inline thread_state::thread_state(const thread_state& t) :
        share(t.share), local(t.local) {

}

/**
 * @brief constructor with shared state and local state
 * @param share: shared state
 * @param local: local  state
 */
inline thread_state::thread_state(const shared_state& share,
        const local_state& local) :
        share(share), local(local) {
    __SAFE_ASSERT__(share < S && local < L);
}

/**
 * @brief print thread state
 * @param out
 * @return ostream
 */
inline ostream& thread_state::to_stream(ostream& out) const {
    out << "(" << share << "|" << local << ")";
    return out;
}

/**
 * @brief overloading operator <<: print thread state
 * @param out
 * @param ts
 * @return ostream
 */
inline ostream& operator<<(ostream& out, const thread_state& t) {
    return t.to_stream(out);
}

/**
 * @brief overloading operator ==
 * @param t1
 * @param t2
 * @return bool
 * 		   true : if t1 == t2
 * 		   false: otherwise
 */
inline bool operator==(const thread_state& t1, const thread_state& t2) {
    return t1.get_share() == t2.get_share() && t1.get_local() == t2.get_local();
}

/**
 * @brief overloading operator !=
 * @param t1
 * @param t2
 * @return bool
 * 		   true : if t1 == t2
 * 		   false: otherwise
 */
inline bool operator!=(const thread_state& t1, const thread_state& t2) {
    return !(t1 == t2);
}

/**
 * @brief overloading operator <
 * @param t1
 * @param t2
 * @return bool
 * 		   true : if t1 < t2
 * 		   false: otherwise
 */
inline bool operator<(const thread_state& t1, const thread_state& t2) {
    if (t1.get_share() == t2.get_share())
        return t1.get_local() < t2.get_local();
    else
        return t1.get_share() < t2.get_share();
}

/**
 * @brief overloading operator >
 * @param t1
 * @param t2
 * @return bool
 * 		   true : if t1 > t2
 * 		   false: otherwise
 */
inline bool operator>(const thread_state& t1, const thread_state& t2) {
    return t2 < t1;
}

/// class global state
///
#ifdef HASHMAP
using ca_locals = unordered_map<local_state, size_p>;
#endif
using ca_locals = map<local_state, size_p>;
class global_state {
public:
    inline global_state();
    inline global_state(const thread_state& t);
    inline global_state(const thread_state& t, const size_p& n);
    inline global_state(const shared_state& share, const ca_locals& locals);
    inline global_state(const global_state& s);

    ~global_state() {
    }

    ostream& to_stream(ostream& out = cout, const string& sep = "|") const;

    inline const ca_locals& get_locals() const {
        return locals;
    }

    inline shared_state get_share() const {
        return share;
    }

private:
    shared_state share;
    ca_locals locals;
};

/**
 * @brief default constructor: initialize
 *        share  = 0
 *        locals = empty map
 */
inline global_state::global_state() :
        share(0), locals(ca_locals()) {
}

/**
 * @brief constructor with a thread state
 * @param t
 */
inline global_state::global_state(const thread_state& t) :
        share(t.get_share()), locals(ca_locals()) {
    locals.emplace(t.get_local(), 1);
}

/**
 * @brief constructor with a thread state and n threads
 * @param t
 * @param n
 */
inline global_state::global_state(const thread_state& t, const size_p& n) :
        share(t.get_share()), locals(ca_locals()) {
    locals.emplace(t.get_local(), n);
}

/**
 * @brief constructor with a shared state and local states
 * @param share : shared state
 * @param locals: local states represented in counter abstraction form
 */
inline global_state::global_state(const shared_state& share,
        const ca_locals& locals) :
        share(share), locals(locals) {
}

/**
 * @brief constructor with a global state
 * @param s
 */
inline global_state::global_state(const global_state& s) :
        share(s.get_share()), locals(s.get_locals()) {

}

/**
 * @brief call by <<
 * @param out
 * @param sep
 * @return
 */
inline ostream& global_state::to_stream(ostream& out, const string& sep) const {
    out << "<" << this->share << "|";
    for (auto iloc = this->locals.begin(); iloc != this->locals.end(); ++iloc) {
        out << "(" << iloc->first << "," << iloc->second << ")";
    }
    out << ">";
    return out;
}

/**
 * @brief overloading operator <<
 * @param out
 * @param g
 * @return
 */
inline ostream& operator<<(ostream& out, const global_state& g) {
    return g.to_stream(out);
}

/**
 * @brief overloading operator <
 * @param s1
 * @param s2
 * @return bool
 * 		   true : if s1 < s2
 * 		   false: otherwise
 */
inline bool operator<(const global_state& s1, const global_state& s2) {
    if (s1.get_share() == s2.get_share()) {
        return COMPARE::compare_map(s1.get_locals(), s2.get_locals()) == -1;
    } else {
        return s1.get_share() < s2.get_share();
    }
}

/**
 * @brief overloading operator >
 * @param s1
 * @param s2
 * @return bool
 * 		   true : if s1 > s2
 * 		   false: otherwise
 */
inline bool operator>(const global_state& s1, const global_state& s2) {
    return s2 < s1;
}

/**
 * @brief overloading operator ==
 * @param s1
 * @param s2
 * @return bool
 * 		   true : if s1 == s2
 * 		   false: otherwise
 */
inline bool operator==(const global_state& s1, const global_state& s2) {
    if (s1.get_share() == s2.get_share()) {
        if (s1.get_locals().size() == s2.get_locals().size()) {
            auto is1 = s1.get_locals().begin(), is2 = s2.get_locals().begin();
            while (is1 != s1.get_locals().end()) {
                if ((is1->first != is2->first) || (is1->second != is2->second))
                    return false;
                ++is1, ++is2;
            }
            return true;
        }
    }
    return false;
}

/**
 * @brief overloading operator !=
 * @param s1
 * @param s2
 * @return bool
 * 		   true : if s1 != s2
 * 		   false: otherwise
 */
inline bool operator!=(const global_state& s1, const global_state& s2) {
    return !(s1 == s2);
}

using vertex = id_thread_state;

enum class type_trans {
    NORM, SPAW, BRCT
};

class transition {
public:
    inline transition(const transition& t);
    inline transition(const vertex& src, const vertex& dst);
    inline transition(const vertex& src, const vertex& dst,
            const type_trans& type);
    ~transition() {
    }

    ostream& to_stream(ostream& out = cout) const;

    inline vertex get_src() const {
        return src;
    }

    inline vertex get_dst() const {
        return dst;
    }

    inline type_trans get_type() const {
        return type;
    }

private:
    vertex src; /// source      of transition
    vertex dst; /// destination of transition
    type_trans type;
};

inline transition::transition(const transition& t) :
        src(t.src), dst(t.dst), type(t.type) {
}

inline transition::transition(const vertex& src, const vertex& dst) :
        src(src), dst(dst), type(type_trans::NORM) {
}

inline transition::transition(const vertex& src, const vertex& dst,
        const type_trans& type) :
        src(src), dst(dst), type(type) {
}

inline ostream& transition::to_stream(ostream& out) const {
    out << src << " ";
    switch (type) {
    case type_trans::BRCT:
        out << "~>";
        break;
    case type_trans::SPAW:
        out << "+>";
        break;
    default:
        out << "->";
        break;
    }
    out << " " << dst;
    return out;
}

/**
 * @brief overloading operator <<: print transition
 * @param out
 * @param ts
 * @return ostream
 */
inline ostream& operator<<(ostream& out, const transition& r) {
    return r.to_stream(out);
}

/**
 * @brief overloading operator ==
 * @param r1
 * @param r2
 * @return bool
 *         true : if r1 == r2
 *         false: otherwise
 */
inline bool operator==(const transition& r1, const transition& r2) {
    return r1.get_src() == r2.get_src() && r1.get_dst() == r2.get_dst();
}

/**
 * @brief overloading operator !=
 * @param r1
 * @param r2
 * @return bool
 *         true : if r1 != r2
 *         false: otherwise
 */
inline bool operator!=(const transition& r1, const transition& r2) {
    return !(r1 == r2);
}

/**
 * @brief overloading operator <
 * @param r1
 * @param r2
 * @return bool
 *         true : if r1 < r2
 *         false: otherwise
 */
inline bool operator<(const transition& r1, const transition& r2) {
    if (r1.get_src() == r2.get_src())
        return r1.get_dst() < r2.get_dst();
    return r1.get_src() < r2.get_src();
}

/**
 * @brief overloading operator >
 * @param r1
 * @param r2
 * @return bool
 *         true : if r1 > r2
 *         false: otherwise
 */
inline bool operator>(const transition& r1, const transition& r2) {
    if (r1.get_src() == r2.get_src())
        return r1.get_dst() > r2.get_dst();
    return r1.get_src() > r2.get_src();
}

using adj_list = vector<deque<id_transition>>;

} /* namespace BSSP */

#endif /* STATE_HH_ */
