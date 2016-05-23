/**
 * @name refs.cc
 *
 * @date: Jun 21, 2015
 * @author: Peizun Liu
 */

#include "refer.hh"

namespace bssp {

refer::refer() {

}

refer::~refer() {

}
bool refer::OPT_INPUT_TTS = false;

bool refer::OPT_PRINT_ADJ = false;
bool refer::OPT_PRINT_CMD = false;
bool refer::OPT_PRINT_ALL = false;

clock_t refer::ELAPSED_TIME = clock();

string refer::TMP_FILENAME = "/tmp/tmp.tts.no_comment";
string refer::COMMENT = "#";

} /* namespace SURA */
