/*********************                                                        */
/*! \file command_executor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#include <cassert>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

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

CommandExecutor::CommandExecutor(Options& options)
    : d_solver(new api::Solver(&options)),
      d_smtEngine(d_solver->getSmtEngine()),
      d_options(options),
      d_stats("driver"),
      d_result()
{
}

void CommandExecutor::flushStatistics(std::ostream& out) const
{
  d_solver->getExprManager()->getStatistics().flushInformation(out);
  d_smtEngine->getStatistics().flushInformation(out);
  d_stats.flushInformation(out);
}

void CommandExecutor::safeFlushStatistics(int fd) const
{
  d_solver->getExprManager()->safeFlushStatistics(fd);
  d_smtEngine->safeFlushStatistics(fd);
  d_stats.safeFlushInformation(fd);
}

bool CommandExecutor::doCommand(Command* cmd)
{
  if( d_options.getParseOnly() ) {
    return true;
  }

  CommandSequence *seq = dynamic_cast<CommandSequence*>(cmd);
  if(seq != nullptr) {
    // assume no error
    bool status = true;

    for (CommandSequence::iterator subcmd = seq->begin();
         status && subcmd != seq->end();
         ++subcmd)
    {
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
  if (d_options.getStatistics())
  {
    flushStatistics(*d_options.getErr());
  }
  /* We have to keep options passed via CL on reset. These options are stored
   * in CommandExecutor::d_options (populated and created in the driver), and
   * CommandExecutor::d_options only contains *these* options since the
   * NodeManager copies the options into a new options object before SmtEngine
   * configures additional options based on the given CL options.
   * We can thus safely reuse CommandExecutor::d_options here. */
  d_solver.reset(new api::Solver(&d_options));
}

bool CommandExecutor::doCommandSingleton(Command* cmd)
{
  bool status = true;
  if(d_options.getVerbosity() >= -1) {
    status = smtEngineInvoke(d_smtEngine, cmd, d_options.getOut());
  } else {
    status = smtEngineInvoke(d_smtEngine, cmd, nullptr);
  }

  Result res;
  const CheckSatCommand* cs = dynamic_cast<const CheckSatCommand*>(cmd);
  if(cs != nullptr) {
    d_result = res = cs->getResult();
  }
  const QueryCommand* q = dynamic_cast<const QueryCommand*>(cmd);
  if(q != nullptr) {
    d_result = res = q->getResult();
  }
 const  CheckSynthCommand* csy = dynamic_cast<const CheckSynthCommand*>(cmd);
  if(csy != nullptr) {
    d_result = res = csy->getResult();
  }

  if((cs != nullptr || q != nullptr) && d_options.getStatsEveryQuery()) {
    std::ostringstream ossCurStats;
    flushStatistics(ossCurStats);
    std::ostream& err = *d_options.getErr();
    printStatsIncremental(err, d_lastStatistics, ossCurStats.str());
    d_lastStatistics = ossCurStats.str();
  }

  // dump the model/proof/unsat core if option is set
  if (status) {
    std::vector<std::unique_ptr<Command> > getterCommands;
    if (d_options.getDumpModels()
        && (res.asSatisfiabilityResult() == Result::SAT
            || (res.isUnknown() && res.whyUnknown() == Result::INCOMPLETE)))
    {
      getterCommands.emplace_back(new GetModelCommand());
    }
    if (d_options.getDumpProofs()
        && res.asSatisfiabilityResult() == Result::UNSAT)
    {
      getterCommands.emplace_back(new GetProofCommand());
    }

    if (d_options.getDumpInstantiations()
        && ((d_options.getInstFormatMode() != options::InstFormatMode::SZS
             && (res.asSatisfiabilityResult() == Result::SAT
                 || (res.isUnknown()
                     && res.whyUnknown() == Result::INCOMPLETE)))
            || res.asSatisfiabilityResult() == Result::UNSAT))
    {
      getterCommands.emplace_back(new GetInstantiationsCommand());
    }

    if (d_options.getDumpSynth() &&
        res.asSatisfiabilityResult() == Result::UNSAT) {
      getterCommands.emplace_back(new GetSynthSolutionCommand());
    }

    if (d_options.getDumpUnsatCores() &&
        res.asSatisfiabilityResult() == Result::UNSAT) {
      getterCommands.emplace_back(new GetUnsatCoreCommand());
    }

    if (!getterCommands.empty()) {
      // set no time limit during dumping if applicable
      if (d_options.getForceNoLimitCpuWhileDump()) {
        setNoLimitCPU();
      }
      for (const auto& getterCommand : getterCommands) {
        status = doCommandSingleton(getterCommand.get());
        if (!status)
        {
          break;
        }
      }
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

void printStatsIncremental(std::ostream& out,
                           const std::string& prvsStatsString,
                           const std::string& curStatsString)
{
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
        const std::streamsize old_precision = out.precision();
        out << curStatName << ", " << curStatValue << " "
            << "(" << std::setprecision(8) << (curFloat-prvsFloat) << ")"
            << std::endl;
        out.precision(old_precision);
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

  while (!iss.eof())
  {
    std::getline(iss, statValue, '\n');

    bool skip = false;
    try
    {
      double dval = std::stod(statValue);
      skip = (dval == 0.0);
    }
    // Value can not be converted, don't skip
    catch (const std::invalid_argument&) {}
    catch (const std::out_of_range&) {}

    skip = skip || (statValue == " \"0\"" || statValue == " \"[]\"");

    if (!skip)
    {
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
