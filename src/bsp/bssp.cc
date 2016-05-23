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
        initl_S(), final_S(), active_R(), active_TS() {
    initl_S = parse_input_SS(s_initl);
    final_S = parse_input_SS(s_final);
    this->parse_input_TTS(filename);
}

/**
 * @brief destructor
 */
BSSP::~BSSP() {
}

/**
 * @brief extract the system state from input
 * @param state
 * @return system state
 */
syst_state BSSP::parse_input_SS(const string& state) {
    if (state.find('|') != std::string::npos) {
        return utils::create_global_state_from_str(state);
    } else { /// str_ts is store in a file
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

            trans_ID++;
        } else {
            throw bws_runtime_error("illegal transition");
        }
    }
    new_in.close();

#ifndef NDEBUG
    cout << "Initial State: " << initl_S << "\n";
    cout << "Final   State: " << final_S << "\n";
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

    this->s_incoming.swap(s_incoming); /// setup s_incoming
}

/**
 * @brief solicit for backward search
 * @return bool:
 *         true : if
 */
bool BSSP::solicit_for_BWS() {

}

} /* namespace bssp */
