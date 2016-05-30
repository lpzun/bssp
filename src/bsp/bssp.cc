/**
 * @brief bssp.cc
 *
 * @date  : May 21, 2016
 * @author: Peizun Liu
 */

#include "bssp.hh"

namespace bssp {

/**
 * @brief constructor
 * @param s_initl
 * @param s_final
 * @param filename
 */
BSSP::BSSP(const string& s_initl, const string& s_final, const string& filename) :
        initl_TS(), final_SS(), active_R(), active_TS(), active_LR(), ///
        uncoverd(), expanded(), worklist(), votelist(),               ///
        ctx(), n_0(ctx.int_const("n0")), r_affix("r"), s_affix("s"),  ///
        l_affix("l"), ssolver(
                (tactic(ctx, "simplify") & tactic(ctx, "solve-eqs")
                        & tactic(ctx, "smt")).mk_solver()),          ///
        s_encoding(), l_encoding() {
    this->initl_TS = this->parse_input_TS(s_initl);
    this->final_SS = this->parse_input_SS(s_final);
    this->parse_input_TTS(filename);
}

/**
 * @brief destructor
 */
BSSP::~BSSP() {
}

/**
 * @brief symbolic pruning backward search
 * @return bool
 */
bool BSSP::symbolic_pruning_BWS() {
    return this->single_threaded_BSSP();
}

/**
 * @brief extract the thread state from input
 * @param state
 * @return system state
 */
thread_state BSSP::parse_input_TS(const string& state) {
    if (state.find('|') == std::string::npos) { /// str_ts is store in a file
        ifstream in(state.c_str());
        if (in.good()) {
            string content;
            std::getline(in, content);
            in.close();
            return utils::create_thread_state_from_str(content);
        } else {
            throw bws_runtime_error(
                    "parse_input_SS: input state file is unknown!");
        }
    }
    return utils::create_thread_state_from_str(state);
}

/**
 * @brief extract the system state from input
 * @param state
 * @return system state
 */
syst_state BSSP::parse_input_SS(const string& state) {
    if (state.find('|') == std::string::npos) { /// str_ts is store in a file
        ifstream in(state.c_str());
        if (in.good()) {
            string content;
            std::getline(in, content);
            in.close();
            return utils::create_global_state_from_str(content);
        } else {
            throw bws_runtime_error(
                    "parse_input_SS: input state file is unknown!");
        }
    }
    return utils::create_global_state_from_str(state);
}

/**
 * @brief parsing input TTS
 * @param filename
 * @param is_self_loop
 */
void BSSP::parse_input_TTS(const string& filename, const bool& is_self_loop) {
    if (filename == "X")  /// no input file
        throw bws_runtime_error("Please assign the input file!");
    /// original input file before removing comments

    ifstream org_in(filename.c_str());
    if (!org_in.good())
        throw bws_runtime_error("Input file does not find!");
    iparser::remove_comments(org_in, refer::TMP_FILENAME, refer::COMMENT);
    org_in.close();

    /// new input file after removing comments
    ifstream new_in("/tmp/tmp.tts.no_comment");

    new_in >> thread_state::S >> thread_state::L;

    active_TS.reserve(thread_state::S * thread_state::L);
    active_R.reserve(thread_state::S * thread_state::L);

    /// s_incoming: incoming transitions for shared states
    /// s_outgoing: outgoing transitions for shared states
    ///    two elements with same index come up with a pair
    /// NOTE: either incoming or outgoing only stores transition id
    vector<incoming> s_incoming(thread_state::S, incoming());
    vector<outgoing> s_outgoing(thread_state::S, outgoing());

    /// l_incoming: incoming transitions for  local states
    /// l_outgoing: outgoing transitions for  local states
    ///    two elements with same index come up with a pair
    /// NOTE: either incoming or outgoing only stores transition id
    vector<incoming> l_incoming(thread_state::L, incoming());
    vector<outgoing> l_outgoing(thread_state::L, outgoing());

    active_LR = vector<incoming>(thread_state::S, incoming());

    id_transition trans_ID = 0;  /// define unique transition ID
    id_thread_state state_ID = 0;  /// define unique thread state ID
    /// define a map to store the id of thread state
    map<thread_state, id_thread_state> map_S_ID;
    vector<vector<bool>> visited_ID(thread_state::S,
            vector<bool>(thread_state::L, false));

    shared_state s1, s2;              /// shared states
    local_state l1, l2;               /// local  states
    string sep;                       /// separator
    id_thread_state id_src_TS, id_dst_TS;
    while (new_in >> s1 >> l1 >> sep >> s2 >> l2) {
        if (!is_self_loop && s1 == s2 && l1 == l2)
            continue; /// remove self loops

        if (sep == "->" || sep == "+>" || sep == "~>") {
            const thread_state src_TS(s1, l1);
            const thread_state dst_TS(s2, l2);

            /// handle (s1, l1)
            if (!visited_ID[s1][l1]) {
                active_TS.emplace_back(src_TS);

                map_S_ID.emplace(src_TS, state_ID);
                id_src_TS = state_ID++;
                visited_ID[s1][l1] = true;
            } else {
                auto ifind = map_S_ID.find(src_TS);
                if (ifind != map_S_ID.end()) {
                    id_src_TS = ifind->second;
                } else {
                    throw bws_runtime_error(
                            "thread state is mistakenly marked!");
                }
            }

            /// handle (s2, l2)
            if (!visited_ID[s2][l2]) {
                active_TS.emplace_back(dst_TS);

                map_S_ID.emplace(dst_TS, state_ID);
                id_dst_TS = state_ID++;
                visited_ID[s2][l2] = true;
            } else {
                auto ifind = map_S_ID.find(dst_TS);
                if (ifind != map_S_ID.end()) {
                    id_dst_TS = ifind->second;
                } else {
                    throw bws_runtime_error(
                            "thread state is mistakenly marked!");
                }
            }

            /// handle transitons
            if (sep == "+>")
                active_R.emplace_back(id_src_TS, id_dst_TS, type_trans::SPAW);
            else if (sep == "~>")
                active_R.emplace_back(id_src_TS, id_dst_TS, type_trans::BRCT);
            else
                active_R.emplace_back(id_src_TS, id_dst_TS, type_trans::NORM);

            if (s1 != s2) {
                s_outgoing[s1].emplace_back(trans_ID);
                s_incoming[s2].emplace_back(trans_ID);
            }

            /// handle local states
            l_outgoing[l1].emplace_back(trans_ID);
            l_incoming[l2].emplace_back(trans_ID);

            active_LR[s2].emplace_back(trans_ID);

            trans_ID++;
        } else {
            throw bws_runtime_error("illegal transition");
        }
    }
    new_in.close();

#ifndef NDEBUG
    cout << "Initial State: " << initl_S << "\n";
    cout << "Final   State: " << final_SS << "\n";
    cout << __func__ << "\n";
    for (auto s = 0; s < thread_state::S; ++s) {
        cout << "shared state " << s << ": (";
        for (const auto& v : s_incoming[s])
        cout << "x" << v << " + ";
        cout << ") - (";
        for (const auto& v : s_outgoing[s])
        cout << "x" << v << " + ";
        cout << ")";
        cout << "\n";
    }

    for (auto l = 0; l < thread_state::L; ++l) {
        cout << "local state " << l << ": (";
        for (const auto& v : l_incoming[l])
        cout << "x" << v << " + ";
        cout << ") - (";
        for (const auto& v : l_outgoing[l])
        cout << "x" << v << " + ";
        cout << ")";
        cout << "\n";
    }

#endif

    if (refer::OPT_PRINT_ADJ || refer::OPT_PRINT_ALL) {
        cout << "The original TTS:" << endl;
        cout << thread_state::S << " " << thread_state::L << "\n";
        for (const auto& r : this->active_R) {
            cout << active_TS[r.get_src()] << " ";
            switch (r.get_type()) {
            case type_trans::BRCT:
                cout << "~>";
                break;
            case type_trans::SPAW:
                cout << "+>";
                break;
            default:
                cout << "->";
                break;
            }
            cout << " " << active_TS[r.get_dst()];
            cout << "\n";
        }
    }

    this->s_encoding = vector<bool>(thread_state::S, false);
    this->l_encoding = vector<bool>(thread_state::L, false);
    this->build_TSE(s_incoming, s_outgoing, l_incoming, l_outgoing);
}

/**
 * @brief the single-threading BWS with symbolic pruning
 * @return bool
 *         true : if final state is coverable
 *         false: otherwise
 */
bool BSSP::single_threaded_BSSP() {
    /// initialize worklist
    worklist.emplace_back(final_SS);
    cout << initl_TS << " " << final_SS << "\n";

    /// the set of already-expanded    system states
    expanded = adj_chain(thread_state::S, antichain());
    /// the set of known uncoverable   system states
    uncoverd = adj_chain(thread_state::S, antichain());

    while (!worklist.empty()) {
        const auto _tau = worklist.front();
        worklist.pop_front();
        DBG_STD(cout << _tau << "\n";)

        const auto& s = _tau.get_share();

        /// step 1: if \exists t \in <expanded> such that
        ///         t <= _tau then discard _tau
        if (!this->is_minimal(_tau, s))
            continue;

        /// step 2: if \exists t \in <uncoverd> such that
        ///         t <= _tau then discard _tau
        if (this->is_uncoverable(_tau, s))
            continue;

        /// step 3: if _tau is uncoverable via symbolic pruning
        if (this->single_threaded_SP(_tau, s))
            continue;

        /// step 4: compute all cover preimages and handle
        ///         them one by one
        const auto& images = this->step(_tau);
        for (const auto& tau : images) {
            DBG_STD(cout << "  " << tau << "\n";)
            /// if tau \in upward(T_init), return true;
            if (is_coverable(tau))
                return true;
            /// otherwise, push tau into the worklist.
            worklist.emplace_back(tau);
        }
        /// step 5: insert _tau into the expanded states
        ///      (1) minimize the set of expanded states
        this->minimize(_tau, expanded[s]);
        ///      (2) append tau to the set of expanded states
        expanded[s].emplace_back(_tau);
    }
    return false;
}

/**
 * @brief the multithreading BWS with symbolic pruning
 * @return bool
 *         true : if final state is coverable
 *         false: otherwise
 */
bool BSSP::multi_threaded_BSSP() {
    /// the set of backward discovered system states
    /// initialize worklist
    votelist.emplace_back(final_SS);
    cout << initl_TS << " " << final_SS << "\n";

    /// the set of already-expanded    system states
    expanded = adj_chain(thread_state::S, antichain());
    /// the set of known uncoverable   system states
    uncoverd = adj_chain(thread_state::S, antichain());

    /// spawn a thread upon a member function
    /// Here I use a lambda expression. This is a clean
    /// and nice solution, if it works
//    std::thread sp([this] { multi_threaded_SP(); } );
//    sp.join();

    return false;
}

void BSSP::multi_threaded_SP(){

}

/**
 * @brief compute _tau's cover preimages
 * @param _tau
 * @return all cover preimages
 */
deque<syst_state> BSSP::step(const syst_state& _tau) {
    deque<syst_state> images; /// the set of cover preimages
    for (const auto& r : this->active_LR[_tau.get_share()]) {
        const auto& tran = active_R[r];
        const auto& prev = active_TS[tran.get_src()];
        const auto& curr = active_TS[tran.get_dst()];
        switch (tran.get_type()) {
        case type_trans::BRCT:
//            cout << "~>";
            break;
        case type_trans::SPAW: {
//            cout << "+>";
            bool is_updated = false;
            const auto& Z = this->update_counter(_tau.get_locals(),
                    curr.get_local(), prev.get_local(), is_updated);
            /// obtain a cover preimage and store it in the <images>
            if (is_updated)
                images.emplace_back(prev.get_share(), Z);
        }
            break;
        default: {
//            cout << "->";
            const auto& Z = this->update_counter(_tau.get_locals(),
                    curr.get_local(), prev.get_local());
            /// obtain a cover preimage and store it in the <images>
            images.emplace_back(prev.get_share(), Z);
        }
            break;
        }
    }
    return images;
}

/**
 * @brief check whether tau is coverable or not
 * @param tau
 * @return bool
 *         true : tau is coverable
 *         false: otherwise
 */
bool BSSP::is_coverable(const syst_state& tau) {
    if (tau.get_share() == initl_TS.get_share()) {
        if (tau.get_locals().size() == 1
                && tau.get_locals().begin()->first == initl_TS.get_local())
            return true;
    }
    return false;
}

/**
 * @brief check whether tau is uncoverable or not.
 * @param tau:
 * @param W  : the set of uncoverable system states
 * @return bool
 *         true : if exists w such that w <= tau
 *         false: otherwise
 */
bool BSSP::is_uncoverable(const syst_state& tau, const shared_state& s) {
    for (const auto& w : uncoverd[s]) {
        if (is_covered(w, tau))
            return true;
    }
    return false;
}

/**
 * @brief symbolic pruning
 * @param tau
 * @param W
 * @return bool
 *
 */
bool BSSP::single_threaded_SP(const syst_state& tau, const shared_state& s) {
    if (solicit_for_TSE(tau)) {
        minimize(tau, uncoverd[s]);
        uncoverd[s].emplace_back(tau);
        return true;
    }
    return false;
}
/**
 * @brief to determine whether tau1 is covered by tau2.
 *        NOTE: this function assumes that the local parts of tau1 and
 *        tau2 are ordered.
 * @param tau1
 * @param tau2
 * @return bool
 *         true : if tau1 <= tau2
 *         false: otherwise
 */
bool BSSP::is_covered(const syst_state& tau1, const syst_state& tau2) {
    if (tau1.get_share() == tau2.get_share()
            && tau1.get_locals().size() <= tau2.get_locals().size()) {
        auto it1 = tau1.get_locals().cbegin();
        auto it2 = tau2.get_locals().cbegin();
        while (it1 != tau1.get_locals().cend()) {
            /// check if it2 reaches to the end
            if (it2 == tau2.get_locals().cend())
                return false;
            /// compare the map's contents
            if (it1->first == it2->first) {
                if (it1->second > it2->second)
                    return false;
                ++it1, ++it2;
            } else if (it1->first > it2->first) {
                ++it2;
            } else {
                return false;
            }
        }
        return true;
    }
    return false;
}

/**
 * @brief to determine if tau is the minimal state in W
 * @param tau:
 * @param W  :
 * @return bool
 *         true :
 *         false:
 */
bool BSSP::is_minimal(const syst_state& tau, const shared_state& s) {
    for (const auto& w : expanded[s]) {
        if (is_covered(w, tau)) {
            DBG_STD(cout << w << " " << tau << "\n";)
            return false;
        }
    }
    return true;
}

/**
 * @brief to determine if tau is the minimal state in W
 * @param tau:
 * @param W  :
 */
void BSSP::minimize(const syst_state& tau, antichain& W) {
    auto iw = W.begin();
    while (iw != W.end()) {
        if (is_covered(tau, *iw)) {
            iw = W.erase(iw);
        } else {
            ++iw;
        }
    }
}

/**
 * @brief update counters
 * @param Z
 * @param dec
 * @param inc
 * @return local states parts
 */
ca_locals BSSP::update_counter(const ca_locals &Z, const local_state &dec,
        const local_state &inc) {
    if (dec == inc)
        return Z;

    auto _Z = Z;

    /// decrease counter: this is executed only when there is a local
    /// state dec in current local part
    auto idec = _Z.find(dec);
    if (idec != _Z.end()) {
        idec->second--;
        if (idec->second == 0)
            _Z.erase(idec);
    }

    auto iinc = _Z.find(inc);
    if (iinc != _Z.end()) {
        iinc->second++;
    } else {
        _Z.emplace(inc, 1);
    }

    return _Z;
}

/**
 * @brief this is used to update counter for spawn transitions
 * @param Z
 * @param dec
 * @param inc
 * @param is_updated
 * @return local states parts
 */
ca_locals BSSP::update_counter(const ca_locals &Z, const local_state &dec,
        const local_state &inc, bool& is_updated) {
    auto _Z = Z;
    auto iinc = _Z.find(inc);
    if (iinc != _Z.end()) {
        /// decrease counter: this is executed only when there is a local
        /// state dec in current local part
        auto idec = _Z.find(dec);
        if (idec != _Z.end()) {
            idec->second--;
            if (idec->second == 0)
                _Z.erase(idec);
        }
        is_updated = true;
    }
    return _Z;
}

/////////////////////////////////////////////////////////////////////////
/// The following are the definitions for symbolic pruning.
///
/////////////////////////////////////////////////////////////////////////

/**
 * @brief solicit if tau is uncoverable
 * @param tau
 * @return bool
 *         true : means unsat, uncoverable
 *         false: means
 */
bool BSSP::solicit_for_TSE(const syst_state& tau) {
    vec_expr assumption(ctx);

    for (size_l l = 0; l < thread_state::L && l_encoding[l]; ++l) {
        auto ifind = tau.get_locals().find(l);
        if (ifind != tau.get_locals().end())
            assumption.push_back(
                    ctx.int_const((l_affix + std::to_string(l)).c_str())
                            == ifind->second);
        else
            assumption.push_back(
                    ctx.int_const((l_affix + std::to_string(l)).c_str()) == 0);
    }

    for (size_l s = 0; s < thread_state::S && s_encoding[s]; ++s) {
        if (s == tau.get_share())
            assumption.push_back(
                    ctx.int_const((s_affix + std::to_string(s)).c_str()) == 1);
        else
            assumption.push_back(
                    ctx.int_const((s_affix + std::to_string(s)).c_str()) == 0);
    }

    switch (ssolver.check(assumption)) {
    case unsat:
        return true;
    default:
        return false;
    }
}

/**
 * @brief build thread state equation formula
 * @param s_incoming
 * @param s_outgoing
 * @param l_incoming
 * @param l_outgoing
 * @return a set of constraints
 */
void BSSP::build_TSE(const vector<incoming>& s_incoming,
        const vector<outgoing>& s_outgoing, ///
        const vector<incoming>& l_incoming, ///
        const vector<outgoing>& l_outgoing) {
    /// step 1: add n_0 >= 1
    this->ssolver.add(n_0 >= 1);
    /// step 2: add x_i >= 0
    for (size_t i = 0; i < active_R.size(); ++i) {
        this->ssolver.add(
                ctx.int_const((r_affix + std::to_string(i)).c_str()) >= 0);
    }

    /// step 1: add C_L constraints
    const auto& c_L = this->build_CL(l_incoming, l_outgoing);
    for (size_t i = 0; i < c_L.size(); ++i) {
        this->ssolver.add(c_L[i]);
    }
    /// step 2: add C_S constraints
    const auto& c_S = this->build_CS(s_incoming, s_outgoing);
    for (size_t i = 0; i < c_S.size(); ++i) {
        this->ssolver.add(c_S[i]);
    }
}

/**
 * @brief build local state constraints
 * @param l_incoming
 * @param l_outgoing
 * @return the vector of constraints
 */
vec_expr BSSP::build_CL(const vector<incoming>& l_incoming,
        const vector<outgoing>& l_outgoing) {
    vec_expr phi(ctx);

    for (size_l l = 0; l < thread_state::L; ++l) {
        if (l_incoming.size() == 0 && l_outgoing.size() == 0)
            continue;

        /// mark shared state s has C_L constraints
        this->l_encoding[l] = true;

        /// declare left-hand  side
        expr lhs(l == initl_TS.get_local() ? n_0 : ctx.int_val(0));
        /// declare right-hand side
        expr rhs(ctx.int_const((l_affix + std::to_string(l)).c_str()));

        /// setup left-hand  side
        for (const auto& inc : l_incoming[l])
            lhs = lhs + ctx.int_const((r_affix + std::to_string(inc)).c_str());
        /// setup right-hand side
        for (const auto& out : l_outgoing[l])
            rhs = rhs + ctx.int_const((r_affix + std::to_string(out)).c_str());

        phi.push_back(lhs >= rhs);
    }
    return phi;
}

/**
 * @brief build shared state constraints
 * @param s_incoming
 * @param s_outgoing
 * @return the vector of constraints
 */
vec_expr BSSP::build_CS(const vector<incoming>& s_incoming,
        const vector<outgoing>& s_outgoing) {
    vec_expr phi(ctx);

    for (size_s s = 0; s < thread_state::S; ++s) {
        if (s_incoming.size() == 0 && s_outgoing.size() == 0)
            continue;

        /// mark shared state s has C_S constraints
        this->s_encoding[s] = true;

        /// declare left-hand  side
        expr lhs(s == initl_TS.get_share() ? ctx.int_val(1) : ctx.int_val(0));
        /// declare right-hand side
        expr rhs(ctx.int_const((s_affix + std::to_string(s)).c_str()));

        /// setup left-hand  side
        for (const auto& inc : s_incoming[s])
            lhs = lhs + ctx.int_const((r_affix + std::to_string(inc)).c_str());
        /// setup right-hand side
        for (const auto& out : s_outgoing[s])
            rhs = rhs + ctx.int_const((r_affix + std::to_string(out)).c_str());

        phi.push_back(lhs == rhs);
    }
    return phi;
}

} /* namespace bssp */
