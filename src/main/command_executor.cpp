/*********************                                                        */
/*! \file command_executor.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds, Kshitij Bansal
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#include "main/command_executor.h"

#ifndef __WIN32__
#  include <sys/resource.h>
#endif /* ! __WIN32__ */

#include <iostream>
#include <string>

#include "main/main.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/printer_options.h"
#include "options/smt_options.h"
#include "smt_util/command.h"


namespace CVC4 {
namespace main {

// Function to cancel any (externally-imposed) limit on CPU time.
// This is used for competitions while a solution (proof or model)
// is being dumped (so that we don't give "sat" or "unsat" then get
// interrupted partway through outputting a proof!).
void setNoLimitCPU() {
  // Windows doesn't have these things, just ignore
#ifndef __WIN32__
  struct rlimit rlc;
  int st = getrlimit(RLIMIT_CPU, &rlc);
  if(st == 0) {
    rlc.rlim_cur = rlc.rlim_max;
    setrlimit(RLIMIT_CPU, &rlc);
  }
#endif /* ! __WIN32__ */
}

void printStatsIncremental(std::ostream& out, const std::string& prvsStatsString, const std::string& curStatsString);

CommandExecutor::CommandExecutor(ExprManager &exprMgr, Options &options) :
  d_exprMgr(exprMgr),
  d_smtEngine(new SmtEngine(&exprMgr)),
  d_options(options),
  d_stats("driver"),
  d_result() {
}

bool CommandExecutor::doCommand(Command* cmd)
{
  if( d_options[options::parseOnly] ) {
    return true;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    // assume no error
    bool status = true;

    for(CommandSequence::iterator subcmd = seq->begin();
        (status || d_options[options::continuedExecution]) && subcmd != seq->end();
        ++subcmd) {
      status = doCommand(*subcmd);
    }

    return status;
  } else {
    if(d_options[options::verbosity] > 2) {
      *d_options[options::out] << "Invoking: " << *cmd << std::endl;
    }

    return doCommandSingleton(cmd);
  }
}

void CommandExecutor::reset()
{
  if(d_options[options::statistics]) {
    flushStatistics(*d_options[options::err]);
  }
  delete d_smtEngine;
  d_smtEngine = new SmtEngine(&d_exprMgr);
}

bool CommandExecutor::doCommandSingleton(Command* cmd)
{
  bool status = true;
  if(d_options[options::verbosity] >= -1) {
    status = smtEngineInvoke(d_smtEngine, cmd, d_options[options::out]);
  } else {
    status = smtEngineInvoke(d_smtEngine, cmd, NULL);
  }

  Result res;
  CheckSatCommand* cs = dynamic_cast<CheckSatCommand*>(cmd);
  if(cs != NULL) {
    d_result = res = cs->getResult();
  }
  QueryCommand* q = dynamic_cast<QueryCommand*>(cmd);
  if(q != NULL) {
    d_result = res = q->getResult();
  }

  if((cs != NULL || q != NULL) && d_options[options::statsEveryQuery]) {
    std::ostringstream ossCurStats;
    flushStatistics(ossCurStats);
    printStatsIncremental(*d_options[options::err], d_lastStatistics, ossCurStats.str());
    d_lastStatistics = ossCurStats.str();
  }

  // dump the model/proof/unsat core if option is set
  if(status) {
    Command* g = NULL;
    if( d_options[options::produceModels] &&
        d_options[options::dumpModels] &&
        ( res.asSatisfiabilityResult() == Result::SAT ||
          (res.isUnknown() && res.whyUnknown() == Result::INCOMPLETE) ) ) {
      g = new GetModelCommand();
    }
    if( d_options[options::proof] &&
        d_options[options::dumpProofs] &&
        res.asSatisfiabilityResult() == Result::UNSAT ) {
      g = new GetProofCommand();
    }
    if( d_options[options::dumpInstantiations] &&
        ( ( d_options[options::instFormatMode] != INST_FORMAT_MODE_SZS &&
            ( res.asSatisfiabilityResult() == Result::SAT || (res.isUnknown() && res.whyUnknown() == Result::INCOMPLETE) ) ) ||
          res.asSatisfiabilityResult() == Result::UNSAT ) ) {
      g = new GetInstantiationsCommand();
    }
    if( d_options[options::dumpSynth] && res.asSatisfiabilityResult() == Result::UNSAT ){
      g = new GetSynthSolutionCommand();
    }
    if( d_options[options::dumpUnsatCores] && res.asSatisfiabilityResult() == Result::UNSAT ) {
      g = new GetUnsatCoreCommand();
    }
    if(g != NULL) {
      // set no time limit during dumping if applicable
      if( d_options[options::forceNoLimitCpuWhileDump] ){
        setNoLimitCPU();
      }
      status = doCommandSingleton(g);
    }
  }
  return status;
}

bool smtEngineInvoke(SmtEngine* smt, Command* cmd, std::ostream *out)
{
  if(out == NULL) {
    cmd->invoke(smt);
  } else {
    cmd->invoke(smt, *out);
  }
  // ignore the error if the command-verbosity is 0 for this command
  if(smt->getOption(std::string("command-verbosity:") + cmd->getCommandName()).getIntegerValue() == 0) {
    return true;
  }
  return !cmd->fail();
}

void printStatsIncremental(std::ostream& out, const std::string& prvsStatsString, const std::string& curStatsString) {
  if(prvsStatsString == "") {
    out << curStatsString;
    return;
  }

  // read each line
  // if a number, subtract and add that to parentheses
  std::istringstream issPrvs(prvsStatsString);
  std::istringstream issCur(curStatsString);

  std::string prvsStatName, prvsStatValue, curStatName, curStatValue;

  std::getline(issPrvs, prvsStatName, ',');
  std::getline(issCur, curStatName, ',');

  /**
   * Stat are assumed to one-per line: "<statName>, <statValue>"
   *   e.g. "sat::decisions, 100"
   * Output is of the form: "<statName>, <statValue> (<statDiffFromPrvs>)"
   *   e.g. "sat::decisions, 100 (20)"
   * If the value is not numeric, no change is made.
   */
  while( !issCur.eof() ) {

    std::getline(issCur, curStatValue, '\n');

    if(curStatName == prvsStatName) {
      std::getline(issPrvs, prvsStatValue, '\n');

      double prvsFloat, curFloat;
      bool isFloat =
        (std::istringstream(prvsStatValue) >> prvsFloat) &&
        (std::istringstream(curStatValue) >> curFloat);

      if(isFloat) {
        out << curStatName << ", " << curStatValue << " "
            << "(" << std::setprecision(8) << (curFloat-prvsFloat) << ")"
            << std::endl;
      } else {
        out << curStatName << ", " << curStatValue << std::endl;
      }

      std::getline(issPrvs, prvsStatName, ',');
    } else {
      out << curStatName << ", " << curStatValue << std::endl;
    }

    std::getline(issCur, curStatName, ',');
  }
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
