/*********************                                                        */
/*! \file smt_globals.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2015  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This class is a light container for globals that used to live
 ** in options. This is NOT a good long term solution, but is a reasonable
 ** stop gap.
 **
 ** This class is a light container for globals that used to live
 ** in options. This is NOT a good long term solution, but is a reasonable
 ** stop gap.
 **/

#include "smt/smt_globals.h"

#include <cerrno>
#include <iostream>
#include <string>
#include <utility>

#include "cvc4autoconfig.h" // Needed for CVC4_REPLAY
#include "expr/expr_stream.h"
#include "options/option_exception.h"
#include "options/parser_options.h"
#include "smt_util/lemma_input_channel.h"
#include "smt_util/lemma_output_channel.h"
#include "smt/smt_options_handler.h"

namespace CVC4 {

SmtGlobals::SmtGlobals()
    : d_gcReplayLog(false)
    , d_replayLog(NULL)
    , d_replayStream(NULL)
    , d_lemmaInputChannel(NULL)
    , d_lemmaOutputChannel(NULL)
{}

SmtGlobals::~SmtGlobals(){
  if(d_gcReplayLog){
    delete d_replayLog;
    d_gcReplayLog = false;
    d_replayLog = NULL;
  }
}

void SmtGlobals::setReplayLog(std::ostream* log){
  d_replayLog = log;
}

void SmtGlobals::setReplayStream(ExprStream* stream) {
  d_replayStream = stream;
}

void SmtGlobals::setLemmaInputChannel(LemmaInputChannel* in) {
  d_lemmaInputChannel = in;
}

void SmtGlobals::setLemmaOutputChannel(LemmaOutputChannel* out) {
  d_lemmaOutputChannel = out;
}

void SmtGlobals::parseReplayLog(std::string optarg) throw (OptionException) {
  if(d_gcReplayLog){
    delete d_replayLog;
    d_gcReplayLog = false;
    d_replayLog = NULL;
  }

  std::pair<bool, std::ostream*> checkResult = checkReplayLogFilename(optarg);
  d_gcReplayLog = checkResult.first;
  d_replayLog = checkResult.second;
}

#warning "TODO: Move checkReplayLogFilename back into options and has calling setReplayLog as a side effect."
std::pair<bool, std::ostream*> SmtGlobals::checkReplayLogFilename(std::string optarg)
    throw (OptionException)
{
#ifdef CVC4_REPLAY
  if(optarg == "") {
    throw OptionException(std::string("Bad file name for --replay-log"));
  } else if(optarg == "-") {
    return std::make_pair(false, &std::cout);
  } else if(!options::filesystemAccess()) {
    throw OptionException(std::string("Filesystem access not permitted"));
  } else {
    errno = 0;
    std::ios_base::openmode out_trunc = std::ofstream::out | std::ofstream::trunc;
    std::ostream* replayLog = new std::ofstream(optarg.c_str(), out_trunc);
    if(replayLog == NULL || !*replayLog) {
      std::stringstream ss;
      ss << "Cannot open replay-log file: `" << optarg << "': "
         << smt::SmtOptionsHandler::__cvc4_errno_failreason();
      throw OptionException(ss.str());
    }
    return std::make_pair(true, replayLog);
  }
#else /* CVC4_REPLAY */
  throw OptionException("The replay feature was disabled in this build of CVC4.");
#endif /* CVC4_REPLAY */
}


} /* namespace CVC4 */
