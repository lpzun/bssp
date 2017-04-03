/**
 * @brief bssp.hh
 *
 * @date  : May 21, 2016
 * @author: Peizun Liu
 */

#ifndef BSP_BSSP_HH_
#define BSP_BSSP_HH_

#include <chrono>
#include <future>
#include <atomic>

#include "z3++.h"

#include "threadsafe_queue.hh"
#include "utilities.hh"

using namespace z3;

using std::future;

namespace bssp {

using syst_state = global_state;
using antichain = deque<ca_locals>;
using adj_chain = vector<antichain>;

/// store all incoming transitions w.r.t. a specific shared/local state
using incoming = deque<id_transition>;
/// store all outgoing transitions w.r.t. a specific shared/local state
using outgoing = deque<id_transition>;

/// Aliasing vector<expr> as vec_expr
using vec_expr = expr_vector;

enum class pruning {
    reach = 0, unreach = 1, unknown = 2
};

class SBSSP {
public:
    SBSSP(const string& s_initl, const string& s_final, const string& filename);
    ~SBSSP();

    bool symbolic_pruning_BWS();
    size_p cutoff_detection();

    inline unsigned long int get_n_pruning() const {
        return n_pruning;
    }

    inline unsigned long int get_n_unknown() const {
        return n_unknown;
    }

    inline unsigned long int get_n_uncover() const {
        return n_uncover;
    }

    inline std::chrono::duration<double> get_elapsed() const {
        return elapsed;
    }

private:
    /////////////////////////////////////////////////////////////////////////
    /// PART 1. The following defines the functions to parsing input TTS.
    ///
    /////////////////////////////////////////////////////////////////////////
    thread_state initl_TS;
    syst_state final_SS;

    vector<transition> active_R; /// TTS in transitions
    vector<thread_state> active_TS; /// thread states
    vector<incoming> active_INC; /// incoming edge for shared states

    map<thread_state, deque<id_transition>> original_TTS;

    /// the set of known uncoverable system states
    adj_chain uncoverd;
    /// the set of already-expanded  system states
    adj_chain expanded;

    void parse_input_TTS(const string& filename, const bool& is_self_loop =
            false);
    syst_state parse_input_SS(const string& state);
    thread_state parse_input_TS(const string& state);

    /////////////////////////////////////////////////////////////////////////
    /// PART 2. The following are the common utilities for image computation.
    ///
    /////////////////////////////////////////////////////////////////////////
    /// image computation
    deque<syst_state> step(const syst_state& _tau);

    bool is_coverable(const syst_state& tau, const syst_state& init);
    bool is_covered(const ca_locals& Z1, const ca_locals& Z2);
    bool is_equal(const ca_locals& Z1, const ca_locals& Z2);
    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc);
    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc, bool& is_spawn);
    // (s1,l1) +> (s2,l2): <s1|l1> +> <s2|l1,l2>
    ca_locals increment_counter(const ca_locals& Z, const local_state& inc);

    /////////////////////////////////////////////////////////////////////////
    /// PART 3. The following code are the definitions for symbolic pruning.
    ///
    /////////////////////////////////////////////////////////////////////////
    /// All expressions, func_decl, etc., appearing in the class must be
    /// defined in same context; otherwise, segmentation fault happens
    context ctx;

    expr n_0; /// counter variable for initial local state

    string r_affix;  /// prefix for marking equation variables
    string s_affix;  /// prefix for local  state equation variables
    string l_affix;  /// prefix for shared state equation variables

    solver ssolver; /// define the solver as a class member

    vector<bool> s_encoding;
    vector<bool> l_encoding;

    unsigned long int n_pruning;
    unsigned long int n_uncover;
    unsigned long int n_unknown;
    std::chrono::duration<double> elapsed;

    bool widen(const syst_state& tau);

    bool single_threaded_SP(const syst_state& tau, const shared_state& s);
    bool solicit_for_TSE(const syst_state& tau);
    void build_TSE(const vector<incoming>& s_incoming,
            const vector<outgoing>& s_outgoing,
            const vector<incoming>& l_incoming,
            const vector<outgoing>& l_outgoing);
    vec_expr build_CS(const vector<incoming>& s_incoming,
            const vector<outgoing>& s_outgoing);
    vec_expr build_CL(const vector<incoming>& l_incoming,
            const vector<outgoing>& l_outgoing);

    /////////////////////////////////////////////////////////////////////////
    /// PART 4. The following are the definitions for single-threading BSSP
    ///
    /////////////////////////////////////////////////////////////////////////
    ///
    /// backward search
    size_p single_threaded_BSSP(const syst_state& sf);
    size_p single_threaded_BSSP(const syst_state& si, const syst_state& sf);

    bool is_uncoverable(const ca_locals& Z, const shared_state& s);
    bool is_minimal(const ca_locals& Z, const shared_state& s);
    void minimize(const ca_locals& Z, const shared_state& s);

    /////////////////////////////////////////////////////////////////////////
    /// PART 5. The following are the definitions for Karp-Miller procedure
    ///
    /////////////////////////////////////////////////////////////////////////
    ///
    /// karp-miller procedure
    bool is_maximal(const syst_state& s, const deque<syst_state>& explored);
    void maximize(const syst_state& s, deque<syst_state>& worklist);
    bool is_reached(const syst_state& s);

    /////////////////////////////////////////////////////////////////////////
    /// PART 6. The following are the definitions for finite-state forward
    /// search and dynamic convergence detection
    ///
    /////////////////////////////////////////////////////////////////////////
    ///
    /// finite-state forward search

    vector<vector<bool>> reachable_TS;
    set<thread_state> unreachable_TS;
    set<thread_state> old_cand_triples;

    bool standard_FWS(const size_p& n, const size_p& s);
    deque<syst_state> step(const syst_state& tau, size_p& spw);
    set<thread_state> extract_cand_triples(const vector<vector<bool>>& R);
    size_p cand_triple_coverability(const set<thread_state>& new_cand_triples);
    bool is_expanded(const ca_locals& Z, const antichain& W);
};

/// Multi-threaded backward coverability analysis with symbolic pruning
///
///
class CBSSP {
public:
    CBSSP(const string& s_initl, const string& s_final, const string& filename);
    ~CBSSP();

    bool symbolic_pruning_BWS();
private:

    /////////////////////////////////////////////////////////////////////////
    /// PART 1. The following defines the functions to parsing input TTS.
    ///
    /////////////////////////////////////////////////////////////////////////
    thread_state initl_TS;
    syst_state final_SS;

    vector<transition> active_R; /// TTS in transitions
    vector<thread_state> active_TS; /// thread states
    vector<incoming> active_LR; /// incoming edge for shared states

    void parse_input_TTS(const string& filename, const bool& is_self_loop =
            false);
    syst_state parse_input_SS(const string& state);
    thread_state parse_input_TS(const string& state);

    /////////////////////////////////////////////////////////////////////////
    /// PART 2. The following are the common utilities for image computation
    ///
    /////////////////////////////////////////////////////////////////////////
    deque<syst_state> step(const syst_state& _tau);

    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc);
    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc, bool& is_spawn);

    bool is_coverable(const syst_state& tau);
    bool is_covered(const ca_locals& Z1, const ca_locals& Z2);
    bool is_uncoverable(const ca_locals& Z, const antichain& W);

    /////////////////////////////////////////////////////////////////////////
    /// PART 3. The following are the definitions for symbolic pruning.
    ///
    /////////////////////////////////////////////////////////////////////////
    /// All expressions, func_decl, etc., appearing in the class must be
    /// defined in same context; otherwise, segmentation fault happens
    context ctx;

    expr n_0; /// counter variable for initial local state

    string r_affix;  /// prefix for marking equation variables
    string s_affix;  /// prefix for local  state equation variables
    string l_affix;  /// prefix for shared state equation variables

    solver ssolver; /// define the solver as a class member

    vector<bool> s_encoding;
    vector<bool> l_encoding;

    bool solicit_for_TSE(const syst_state& tau);
    void build_TSE(const vector<incoming>& s_incoming,
            const vector<outgoing>& s_outgoing,
            const vector<incoming>& l_incoming,
            const vector<outgoing>& l_outgoing);
    vec_expr build_CS(const vector<incoming>& s_incoming,
            const vector<outgoing>& s_outgoing);
    vec_expr build_CL(const vector<incoming>& l_incoming,
            const vector<outgoing>& l_outgoing);

    /////////////////////////////////////////////////////////////////////////
    /// PART 4. The following are the definitions for multi-threading BSSP
    ///
    /////////////////////////////////////////////////////////////////////////
    ///

    /// the set of already-expanded    system states
    threadsafe_queue<syst_state> cworklist;
    threadsafe_queue<syst_state> cvotelist;

    std::atomic<bool> RUNNING;
    std::atomic<bool> TERMINATE;

    bool multi_threaded_BSSP();
    bool multi_threaded_BS();
    void multi_threaded_SP();

    bool is_minimal(const ca_locals& Z, const antichain& W);
    void minimize(const ca_locals& Z, antichain& W);
};

} /* namespace bssp */

#endif /* BSP_BSSP_HH_ */
