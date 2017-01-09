/*********************                                                        */
/*! \file command_executor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#include "smt/command.h"


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
  d_result(),
  d_replayStream(NULL)
{}

void CommandExecutor::setReplayStream(ExprStream* replayStream) {
  assert(d_replayStream == NULL);
  d_replayStream = replayStream;
  d_smtEngine->setReplayStream(d_replayStream);
}

bool CommandExecutor::doCommand(Command* cmd)
{
  if( d_options.getParseOnly() ) {
    return true;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != NULL) {
    // assume no error
    bool status = true;

    for(CommandSequence::iterator subcmd = seq->begin();
        (status || d_options.getContinuedExecution()) && subcmd != seq->end();
        ++subcmd) {
      status = doCommand(*subcmd);
    }

    return status;
  } else {
    if(d_options.getVerbosity() > 2) {
      *d_options.getOut() << "Invoking: " << *cmd << std::endl;
    }

    return doCommandSingleton(cmd);
  }
}

void CommandExecutor::reset()
{
  if(d_options.getStatistics()) {
    flushStatistics(*d_options.getErr());
  }
  delete d_smtEngine;
  d_smtEngine = new SmtEngine(&d_exprMgr);
}

bool CommandExecutor::doCommandSingleton(Command* cmd)
{
  bool status = true;
  if(d_options.getVerbosity() >= -1) {
    status = smtEngineInvoke(d_smtEngine, cmd, d_options.getOut());
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
  CheckSynthCommand* csy = dynamic_cast<CheckSynthCommand*>(cmd);
  if(csy != NULL) {
    d_result = res = csy->getResult();
  }

  if((cs != NULL || q != NULL) && d_options.getStatsEveryQuery()) {
    std::ostringstream ossCurStats;
    flushStatistics(ossCurStats);
    std::ostream& err = *d_options.getErr();
    printStatsIncremental(err, d_lastStatistics, ossCurStats.str());
    d_lastStatistics = ossCurStats.str();
  }

  // dump the model/proof/unsat core if option is set
  if (status) {
    Command* g = NULL;
    if (d_options.getProduceModels() && d_options.getDumpModels() &&
        (res.asSatisfiabilityResult() == Result::SAT ||
         (res.isUnknown() && res.whyUnknown() == Result::INCOMPLETE))) {
      g = new GetModelCommand();
    }
    if (d_options.getProof() && d_options.getDumpProofs() &&
        res.asSatisfiabilityResult() == Result::UNSAT) {
      g = new GetProofCommand();
    }

    if (d_options.getDumpInstantiations() &&
        ((d_options.getInstFormatMode() != INST_FORMAT_MODE_SZS &&
          (res.asSatisfiabilityResult() == Result::SAT ||
           (res.isUnknown() && res.whyUnknown() == Result::INCOMPLETE))) ||
         res.asSatisfiabilityResult() == Result::UNSAT)) {
      g = new GetInstantiationsCommand();
    }

    if (d_options.getDumpSynth() &&
        res.asSatisfiabilityResult() == Result::UNSAT) {
      g = new GetSynthSolutionCommand();
    }

    if (d_options.getDumpUnsatCores() &&
        res.asSatisfiabilityResult() == Result::UNSAT) {
      g = new GetUnsatCoreCommand();
    }

    if (g != NULL) {
      // set no time limit during dumping if applicable
      if (d_options.getForceNoLimitCpuWhileDump()) {
        setNoLimitCPU();
      }
      status = doCommandSingleton(g);
      delete g;
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
  std::string commandName =
      std::string("command-verbosity:") + cmd->getCommandName();
  if(smt->getOption(commandName).getIntegerValue() == 0) {
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

void CommandExecutor::printStatsFilterZeros(std::ostream& out,
                                            const std::string& statsString) {
  // read each line, if a number, check zero and skip if so
  // Stat are assumed to one-per line: "<statName>, <statValue>"

  std::istringstream iss(statsString);
  std::string statName, statValue;

  std::getline(iss, statName, ',');

  while( !iss.eof() ) {

    std::getline(iss, statValue, '\n');

    double curFloat;
    std::istringstream iss_stat_value (statValue);
    iss_stat_value >> curFloat;
    bool isFloat = iss_stat_value.good();

    if( (isFloat && curFloat == 0) ||
        statValue == " \"0\"" ||
        statValue == " \"[]\"") {
      // skip
    } else {
      out << statName << "," << statValue << std::endl;
    }

    std::getline(iss, statName, ',');
  }

}

void CommandExecutor::flushOutputStreams() {
  if(d_options.getStatistics()) {
    if(d_options.getStatsHideZeros() == false) {
      flushStatistics(*(d_options.getErr()));
    } else {
      std::ostringstream ossStats;
      flushStatistics(ossStats);
      printStatsFilterZeros(*(d_options.getErr()), ossStats.str());
    }
  }

  // make sure out and err streams are flushed too
  d_options.flushOut();
  d_options.flushErr();
}

}/* CVC4::main namespace */
}/* CVC4 namespace */
