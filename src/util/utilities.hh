/**
 * @name utilities.hh
 *
 * @date  : Jun 23, 2015
 * @author: Peizun Liu
 */

#ifndef UTILITIES_HH_
#define UTILITIES_HH_

#include "heads.hh"
#include "refer.hh"

namespace bssp {
/**
 * @brief a tool class that defines utilities
 */
class utils {
public:
    utils();
     ~utils();
    static thread_state create_thread_state_from_str(const string& s_ts,
            const char& delim = '|');
    static thread_state create_thread_state_from_gs_str(const string& s_ts,
            const char& delim = '|');

    static void print_adj_list(
            const map<thread_state, set<thread_state> >& adj_list,
            ostream& out = cout);
    static void print_adj_list(
            const map<thread_state, deque<thread_state> >& adj_list,
            ostream& out = cout);

};

/**
 * @brief the input parser that parses TTS
 */
class iparser {
public:
    static void remove_comments(istream& in, const string& filename,
            const string& comment);
    static void remove_comments(const string& in, string& out,
            const string& comment);

private:
    static void remove_comments(istream& in, ostream& out,
            const string& comment);
    static bool getline(istream& in, string& line, const char& eol = '\n');
};
} /* namespace SURA */

#endif /* UTILITIES_HH_ */
