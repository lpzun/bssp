/**
 * @name utilities.hh
 *
 * @date  : Jun 23, 2015
 * @author: Peizun Liu
 */

#include "utilities.hh"

namespace bssp {

utils::utils() {
    // TODO Auto-generated constructor stub

}

utils::~utils() {
    // TODO Auto-generated destructor stub
}

/**
 *
 * @param s_ts
 * @param delim
 * @return
 */
thread_state utils::create_thread_state_from_str(const string& s_ts,
        const char& delim) {
    deque<string> vs_ts = PPRINT::split(s_ts, delim);
    if (vs_ts.size() != 2) {
        throw("The format of thread state is wrong.");
    }
    return thread_state(stoi(vs_ts[0]), stoi(vs_ts[1]));
}

/**
 *
 * @param s_ts
 * @param delim
 * @return
 */
global_state utils::create_global_state_from_str(const string& s_ts,
        const char& delim) {
    auto vs_ts = PPRINT::split(s_ts, delim);
    if (vs_ts.size() != 2) {
        throw bws_runtime_error("The format of global state is wrong.");
    }
    auto vs_locals = PPRINT::split(vs_ts[1], ',');
    ca_locals locals;
    for (const auto& l : vs_locals)
        locals[stoi(l)]++;
    return global_state(stoi(vs_ts[0]), locals);
}
/**
 * @brief print all of the transitions in the thread-state transition diagram
 * @param adjacency_list
 * @param out
 */
void utils::print_adj_list(
        const map<thread_state, set<thread_state> >& adj_list, ostream& out) {
    out << thread_state::L << " " << thread_state::S << endl;
    for (auto iu = adj_list.begin(); iu != adj_list.end(); ++iu)
        for (auto iv = iu->second.begin(); iv != iu->second.end(); ++iv)
            out << iu->first << " -> " << (*iv) << endl;
}

/**
 * @brief print all of the transitions in the thread-state transition diagram
 * @param adjacency_list
 * @param out
 */
void utils::print_adj_list(
        const map<thread_state, deque<thread_state> >& adj_list, ostream& out) {
    out << thread_state::L << " " << thread_state::S << endl;
    for (auto iu = adj_list.begin(); iu != adj_list.end(); ++iu)
        for (auto iv = iu->second.begin(); iv != iu->second.end(); ++iv)
            out << iu->first << " -> " << (*iv) << endl;
}

/**
 * @brief remove the comments of .ttd files
 * @param in
 * @param filename
 * @param comment
 */
void iparser::remove_comments(istream& in, const string& filename,
        const string& comment) {
    ofstream out(filename.c_str());
    remove_comments(in, out, comment);
}

/**
 * @brief remove the comments of .ttd files
 * @param in
 * @param out
 * @param comment
 */
void iparser::remove_comments(const string& in, string& out,
        const string& comment) {
    std::istringstream instream(in);
    std::ostringstream outstream;
    remove_comments(instream, outstream, comment);
    out = outstream.str();
}

void iparser::remove_comments(istream& in, ostream& out,
        const string& comment) {
    string line;
    while (getline(in, line = "")) {
        const size_t comment_start = line.find(comment);
        out
                << (comment_start == string::npos ?
                        line : line.substr(0, comment_start)) << endl;
    }
}

bool iparser::getline(istream& in, string& line, const char& eol) {
    char c = 0;
    while (in.get(c) ? c != eol : false)
        line += c;
    return c != 0;
}
} /* namespace SURA */
