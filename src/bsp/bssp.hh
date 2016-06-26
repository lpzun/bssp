/**
 * @brief bssp.hh
 *
 * @date  : May 21, 2016
 * @author: Peizun Liu
 */

#ifndef BSP_SBSSP_HH_
#define BSP_SBSSP_HH_

#include <chrono>

#include "z3++.h"

#include "../util/threadsafe_queue.hh"
#include "../util/utilities.hh"

using namespace z3;

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

enum class tse {
    reach = 0, unreach = 1, unknown = 2
};

class SBSSP {
public:
    SBSSP(const string& s_initl, const string& s_final, const string& filename);
    ~SBSSP();

    bool symbolic_pruning_BWS();

    unsigned long int get_n_pruning() const {
        return n_pruning;
    }

    unsigned long int get_n_unknown() const {
        return n_unknown;
    }

    unsigned long int get_n_uncover() const {
        return n_uncover;
    }

    std::chrono::duration<double> get_elapsed() const {
        return elapsed;
    }

private:
    /////////////////////////////////////////////////////////////////////////
    /// PART 1. The following code are the definitions of backward search.
    ///
    /////////////////////////////////////////////////////////////////////////
    thread_state initl_TS;
    syst_state final_SS;

    vector<transition> active_R; /// TTS in transitions
    vector<thread_state> active_TS; /// thread states
    vector<incoming> active_LR; /// incoming edge for shared states

    /// the set of known uncoverable   system states
    adj_chain uncoverd;
    /// the set of already-expanded    system states
    adj_chain expanded;

    void parse_input_TTS(const string& filename, const bool& is_self_loop =
            false);
    syst_state parse_input_SS(const string& state);
    thread_state parse_input_TS(const string& state);

    /// backward search
    bool single_threaded_BSSP();

    /// image computation
    deque<syst_state> step(const syst_state& _tau);

    bool is_coverable(const syst_state& tau);
    bool is_uncoverable(const ca_locals& Z, const shared_state& s);
    bool is_covered(const ca_locals& Z1, const ca_locals& Z2);
    bool is_minimal(const ca_locals& Z, const shared_state& s);
    void minimize(const ca_locals& Z, const shared_state& s);

    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc);
    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc, bool& is_spawn);

    /////////////////////////////////////////////////////////////////////////
    /// PART 2. The following code are the definitions for symbolic pruning.
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
};

} /* namespace bssp */

#endif /* BSP_SBSSP_HH_ */
