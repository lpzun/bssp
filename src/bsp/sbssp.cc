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
SBSSP::SBSSP(const string& s_initl, const string& s_final,
        const string& filename) :
        initl_TS(), final_SS(), active_R(), active_TS(), active_INC(), ///
        uncoverd(), expanded(), ctx(), n_0(ctx.int_const("n0")),       ///
        r_affix("r"), s_affix("s"), l_affix("l"), ssolver(
                (tactic(ctx, "simplify") & tactic(ctx, "solve-eqs")
                        & tactic(ctx, "smt")).mk_solver()),            ///
        s_encoding(), l_encoding(), n_pruning(0), n_uncover(0),        ///
        n_unknown(0), elapsed() {
    this->initl_TS = this->parse_input_TS(s_initl);
    this->final_SS = this->parse_input_SS(s_final);
    this->parse_input_TTS(filename);
}

/**
 * @brief destructor
 */
SBSSP::~SBSSP() {
}

/**
 * @brief symbolic pruning backward search
 * @return bool
 */
bool SBSSP::symbolic_pruning_BWS() {
    return this->single_threaded_BSSP(final_SS);
}

/**
 * @brief extract the thread state from input
 * @param state
 * @return system state
 */
thread_state SBSSP::parse_input_TS(const string& state) {
    if (state.find('|') == std::string::npos) { /// state is store in a file
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
syst_state SBSSP::parse_input_SS(const string& state) {
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
void SBSSP::parse_input_TTS(const string& filename, const bool& is_self_loop) {
    if (filename == "X")  /// no input file
        throw bws_runtime_error("Please assign the input file!");

    /// original input file before removing comments
    ifstream org_in(filename.c_str());
    if (!org_in.good())
        throw bws_runtime_error("Input file does not exist!");
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

    active_INC = vector<incoming>(thread_state::S, incoming());

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

            active_INC[s2].emplace_back(trans_ID);

            original_TTS[src_TS].emplace_back(trans_ID);

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
 * @param sf: target state
 * @return size_p
 *          > 0: final state is coverable with that # of threads
 *          = 0: uncoverable
 */
size_p SBSSP::single_threaded_BSSP(const syst_state& sf) {
    return single_threaded_BSSP(syst_state(initl_TS), sf);
}

/**
 * @brief the single-threading BWS with symbolic pruning
 * @param si: initial state
 * @param sf: target state
 * @return size_p
 *          > 0: final state is coverable with that # of threads
 *          = 0: uncoverable
 */
size_p SBSSP::single_threaded_BSSP(const syst_state& si, const syst_state& sf) {
    /// the set of backward discovered system states
    deque<syst_state> worklist;
    /// initialize worklist
    worklist.emplace_back(sf);
    //cout << si << " " << sf << "\n";

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
        if (!is_minimal(_tau.get_locals(), s)) {
            continue;
        }

        /// step 2: if \exists t \in <uncoverd> such that
        ///         t <= _tau then discard _tau
        if (is_uncoverable(_tau.get_locals(), s)) {
#ifdef STATISTIC
            ++n_pruning;
#endif
            continue;
        }

        /// step 3: if _tau is uncoverable via symbolic pruning
        if (single_threaded_SP(_tau, s)) {
            // if (widen(_tau)) {
            continue;
        }

        /// step 4: compute all cover preimages and handle
        ///         them one by one
        const auto& images = this->step(_tau);
        for (const auto& tau : images) {
            DBG_STD(cout << "  " << tau << "\n";)
            /// if tau \in upward(T_init), return true;
            if (is_coverable(tau, si))
                return tau.get_locals().begin()->second;

            /// otherwise, push tau into the worklist.
            worklist.emplace_back(tau);
        }
        /// step 5: insert _tau into the expanded states
        ///      (1) minimize the set of expanded states
        this->minimize(_tau.get_locals(), s);
        ///      (2) append tau to the set of expanded states
        expanded[s].emplace_back(_tau.get_locals());
    }
    return 0; /// unreachable
}

/**
 * @brief compute _tau's cover preimages
 * @param _tau
 * @return all cover preimages
 */
deque<syst_state> SBSSP::step(const syst_state& _tau) {
    deque<syst_state> images; /// the set of cover preimages
    for (const auto& r : this->active_INC[_tau.get_share()]) {
        const auto& tran = active_R[r];
        const auto& prev = active_TS[tran.get_src()];
        const auto& curr = active_TS[tran.get_dst()];
        switch (tran.get_type()) {
        case type_trans::BRCT: {
        }
            break;
        case type_trans::SPAW: {
            bool is_updated = false;
            const auto& Z = this->update_counter(_tau.get_locals(),
                    curr.get_local(), prev.get_local(), is_updated);
            /// obtain a cover preimage and store it in the <images>
            if (is_updated)
                images.emplace_back(prev.get_share(), Z);
        }
            break;
        default: {
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
bool SBSSP::is_coverable(const syst_state& tau, const syst_state& init) {
    if (tau.get_share() == init.get_share()) {
        if (tau.get_locals().size() == 1
                && tau.get_locals().begin()->first
                        == init.get_locals().begin()->first)
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
bool SBSSP::is_uncoverable(const ca_locals& Z, const shared_state& s) {
    for (const auto& w : uncoverd[s]) {
        if (is_covered(w, Z))
            return true;
    }
    return false;
}

/**
 * This is a procedure for widen a system state tau
 * @param tau
 * @return bool
 */
bool SBSSP::widen(const syst_state& tau) {
    for (const auto& p : tau.get_locals()) {
        syst_state w(tau.get_share(), p.first, p.second);
        if (single_threaded_SP(w, tau.get_share())) {
            return true;
        }
    }
    return single_threaded_SP(tau, tau.get_share());
}

/**
 * @brief symbolic pruning
 * @param tau
 * @param W
 * @return bool
 *
 */
bool SBSSP::single_threaded_SP(const syst_state& tau, const shared_state& s) {
    if (solicit_for_TSE(tau)) {
        minimize(tau.get_locals(), s);
        uncoverd[s].emplace_back(tau.get_locals());
        return true;
    }
    return false;
}

/**
 * To determine whether counter-abstracted local state part Z1 is covered
 * by counter-abstracted local state tau2.
 *        NOTE: this function assumes that both Z1 and Z2 are ordered.
 * @param Z1
 * @param Z1
 * @return bool
 *         true : if tau1 <= tau2
 *         false: otherwise
 */
bool SBSSP::is_covered(const ca_locals& Z1, const ca_locals& Z2) {
    if (Z1.size() > Z2.size())
        return false;

    auto it1 = Z1.cbegin();
    auto it2 = Z2.cbegin();
    while (it1 != Z1.cend()) {
        /// check if it2 reaches to the end
        if (it2 == Z2.cend())
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
#ifdef HASHMAP
    while (it1 != Z1.cend()) {
        auto ifind = Z2.find(it1->first);
        if (ifind == Z2.end() || ifind->second < it1->second)
        return false;
        ++it1;
    }
#endif
    return true;
}

/**
 * @brief to determine if tau is the minimal state in W
 * @param tau:
 * @param W  :
 * @return bool
 *         true :
 *         false:
 */
bool SBSSP::is_minimal(const ca_locals& Z, const shared_state& s) {
    for (const auto& w : expanded[s]) {
        if (is_covered(w, Z)) {
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
void SBSSP::minimize(const ca_locals& Z, const shared_state& s) {
    auto iw = expanded[s].begin();
    while (iw != expanded[s].end()) {
        if (is_covered(Z, *iw)) {
            iw = expanded[s].erase(iw);
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
ca_locals SBSSP::update_counter(const ca_locals &Z, const local_state &dec,
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
ca_locals SBSSP::update_counter(const ca_locals &Z, const local_state &dec,
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

ca_locals SBSSP::increment_counter(const ca_locals& Z, const local_state& inc) {
    auto _Z = Z;
    _Z[inc]++;
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
bool SBSSP::solicit_for_TSE(const syst_state& tau) {
#ifdef STATISTIC
    const auto start = std::chrono::high_resolution_clock::now();
#endif
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
    const auto& result = ssolver.check(assumption);

#ifdef STATISTIC
    const auto& end = std::chrono::high_resolution_clock::now();
    elapsed += std::chrono::duration_cast<std::chrono::milliseconds>(
            end - start);
#endif
    switch (result) {
    case unsat:
#ifdef STATISTIC
        ++n_uncover;
#endif
        return true;
    default:
#ifdef STATISTIC
        ++n_unknown;
#endif
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
void SBSSP::build_TSE(const vector<incoming>& s_incoming,
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
vec_expr SBSSP::build_CL(const vector<incoming>& l_incoming,
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
vec_expr SBSSP::build_CS(const vector<incoming>& s_incoming,
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

/////////////////////////////////////////////////////////////////////////
/// PART 6. The following are the definitions for Finite-Ftate Forward
/// Search and dynamic convergence detection
///
/////////////////////////////////////////////////////////////////////////

/**
 * One interesting point: we add some on-the-fly flavor when extract the
 * candidate triples.
 *
 * @return the convergence
 */
size_p SBSSP::cutoff_detection() {
    reached_TS = vector<vector<bool>>(thread_state::S,
            vector<bool>(thread_state::S, false));
    size_p n = 1;
    size_p s = 1;
    while (true) {
        cout << "With >= " << n << " threads, candidate triples are:\n";
        standard_FWS(n++, s);
        auto p = extract_candidate_triples(reached_TS);
        if (p.second > n)
            n = p.second;
        if (p.first == 0)
            return --n;
    }
    return n;
}

/**
 * @brief this is based on breadth-first search
 * @param n : the number of initial threads
 * @param s : the number of spawn   threads
 * @return bool
 *         true : if final state is reachable under n threads and s spawns
 *         false: otherwise
 */
bool SBSSP::standard_FWS(const size_p& n, const size_p& s) {
    // cout<<n<<"========================\n"; // delete----------------
    auto spw = s;       /// the upper bound of spawns that can be fired
    deque<syst_state> worklist;
    deque<syst_state> explored;

    worklist.emplace_back(initl_TS, n);
    reached_TS[initl_TS.get_share()][initl_TS.get_local()] = true;
    while (!worklist.empty()) {
        const auto tau = worklist.front();
        worklist.pop_front();

        /// step 1: if upward(tau) is already explored, then
        ///         discard it
        if (!this->is_maximal(tau, explored))
            continue;

        /// step 2: compute all post images; check if final
        ///         state is coverable; maximize <worklist>
        const auto& images = step(tau, spw);
        for (const auto& _tau : images) {
            /// return true if _tau covers final state
            if (false && is_reached(_tau))
                return true;
            /// if upward(_tau) already exists, then discard it
            if (!is_maximal(_tau, worklist))
                continue;
            /// maximize <worklist> in term of _tau
            maximize(_tau, worklist);
            worklist.emplace_back(_tau);        /// insert into worklist
        }
        /// maximize <explored> in term of tau
        this->maximize(tau, explored);
        explored.emplace_back(tau); /// insert into explored
    }
    return false;
}

/**
 * @brief image computation for finite state search
 * @param tau
 * @param spw
 * @return the set of post images
 */
deque<syst_state> SBSSP::step(const syst_state& tau, size_p& spw) {
    deque<syst_state> images;

    const auto& s = tau.get_share();
    for (const auto& p : tau.get_locals()) {
        const auto& l = p.first;
        const thread_state curr(s, l);

        auto ifind = this->original_TTS.find(curr);
        if (ifind != this->original_TTS.end()) {
            for (const auto r : ifind->second) {
                const auto& tran = active_R[r];
                const auto& curr = active_TS[tran.get_src()];
                const auto& post = active_TS[tran.get_dst()];
                switch (tran.get_type()) {
                case type_trans::BRCT: {

                }
                    break;
                case type_trans::SPAW: {
                    if (spw <= 0)
                        continue;
                    --spw;
                    /// update counters in term of spawn  transition
                    const auto& _Z = this->increment_counter(tau.get_locals(),
                            post.get_local());
                    images.emplace_back(post.get_share(), _Z);

                    /// compute new reachable thread states
                    reached_TS[post.get_share()][post.get_local()] = true;
                    if (post.get_share() != curr.get_share()) {
                        for (const auto& p : _Z)
                            reached_TS[post.get_share()][p.first] = true;
                    }
                }
                    break;
                default: {
                    /// update counters in term of normal transition
                    const auto& _Z = this->update_counter(tau.get_locals(),
                            curr.get_local(), post.get_local());
                    images.emplace_back(post.get_share(), _Z);

                    /// compute new reachable thread states
                    reached_TS[post.get_share()][post.get_local()] = true;
                    if (post.get_share() != curr.get_share()) {
                        for (const auto& p : _Z)
                            reached_TS[post.get_share()][p.first] = true;
                    }
                }
                    break;
                }
            }
        }
    }
    return images;
}

/**
 * @brief check if some already-explored state covers s, and maximize explored
 * @param s
 * @param explored
 * @return
 */
bool SBSSP::is_maximal(const syst_state& s, const deque<syst_state>& explored) {
    for (auto itau = explored.begin(); itau != explored.end(); ++itau) {
        if (this->is_covered(s.get_locals(), itau->get_locals())) {
            return false;
        }
    }
    return true;
}

/**
 * @brief maximize
 * @param worklist
 */
void SBSSP::maximize(const syst_state& s, deque<syst_state>& worklist) {
    for (auto itau = worklist.begin(); itau != worklist.end();) {
        if (this->is_covered(itau->get_locals(), s.get_locals())) {
            itau = worklist.erase(itau);
        } else {
            ++itau;
        }
    }
}

bool SBSSP::is_reached(const syst_state& s) {
    return false;
}

/**
 *
 * @param R: the set of reachable thread states
 * @return the number of candidate triples
 */
pair<int, size_p> SBSSP::extract_candidate_triples(
        const vector<vector<bool>>& R) {
    int cnt = 0;
    size_p n = 0;
    for (auto s = 0; s < thread_state::S; ++s) {
        for (auto l = 0; l < thread_state::L; ++l) {
            if (!R[s][l]) // unreachable thread state
                continue;
            /// candidate triples
            /// u    v <= this is the candidate reachable thread state
            /// |    |
            /// p    q
            thread_state p(s, l);
            auto ifind = this->original_TTS.find(p);
            /// p has no successors
            if (ifind == this->original_TTS.end()) {
                continue;
            }
            /// otherwise
            for (const auto id : ifind->second) { // successors
                const auto& tran = active_R[id];
                const auto& u = active_TS[tran.get_dst()];
                if (p.get_share() == u.get_share())
                    continue;
                for (auto local = 0; local < thread_state::L; ++local) {
                    if (local != u.get_local()) {
                        thread_state q(p.get_share(), local);
                        thread_state v(u.get_share(), local);
                        if (R[q.get_share()][q.get_local()]
                                && !R[v.get_share()][v.get_local()]
                                && unreached_TS.find(v) == unreached_TS.end()) {
                            cout << "p = " << p << ", q = " << q << ", u = "
                                    << u << ", v = " << v << "\n";
                            n = std::max(n,
                                    single_threaded_BSSP(syst_state(v)));
                            if (n > 0) {
                                ++cnt;
                                reached_TS[v.get_share()][v.get_local()] = true;
                            } else {
                                unreached_TS.emplace(v);
                            }

                        }
                    }
                }
            }
        } /// end of enumerating local states
    } /// end of enumerating shared states
    return std::make_pair(cnt, n);
}

}
/* namespace bssp */
