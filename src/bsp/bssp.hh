/**
 * @brief bssp.hh
 *
 * @date  : May 21, 2016
 * @author: Peizun Liu
 */

#ifndef BSP_BSSP_HH_
#define BSP_BSSP_HH_

#include "z3++.h"
#include "../util/utilities.hh"

using namespace z3;

namespace bssp {

using syst_state = global_state;
using antichain = vector<deque<syst_state>>;

/// store all incoming transitions w.r.t. a specific shared/local state
using incoming = deque<id_transition>;
/// store all outgoing transitions w.r.t. a specific shared/local state
using outgoing = deque<id_transition>;

/// Aliasing vector<expr> as vec_expr
using vec_expr = vector<expr>;

enum class tse {
    reach = 0, unreach = 1, unknown = 2
};

class BSSP {
public:
    BSSP(const string& s_initl, const string& s_final, const string& filename);
    ~BSSP();

    bool symbolic_pruning_BWS();

private:
    syst_state initl_S;
    syst_state final_S;

    vector<transition> active_R; /// TTS in transitions
    vector<thread_state> active_TS; /// thread states

    vector<incoming> s_incoming; /// incoming edge for shared states

    void parse_input_TTS(const string& filename, const bool& is_self_loop =
            false);
    syst_state parse_input_SS(const string& state);

    /// backward search
    bool solicit_for_BWS();
    deque<syst_state> step(const syst_state& _tau);

    bool is_reached(const syst_state& tau);
    bool is_covered(const syst_state& tau1, const syst_state& tau2);
    bool is_minimal(const syst_state& tau, const antichain& W);
    void minimize(const syst_state& tau, antichain& W);

    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc);
    ca_locals update_counter(const ca_locals& Z, const local_state& dec,
            const local_state& inc, const bool& is_spawn);

    /// symbolic pruning
    bool solicit_for_TSE(const syst_state& tau);
    vec_expr build_TSE(const vector<incoming>& s_incoming,
            const vector<outgoing>& s_outgoing,
            const vector<incoming>& l_incoming,
            const vector<outgoing>& l_outgoing);
    vec_expr build_CS(const vector<incoming>& s_incoming,
            const vector<outgoing>& s_outgoing);
    vec_expr build_CL(const vector<incoming>& l_incoming,
            const vector<outgoing>& l_outgoing);
};

} /* namespace bssp */

#endif /* BSP_BSSP_HH_ */
