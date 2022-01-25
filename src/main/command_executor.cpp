/******************************************************************************
 * Top contributors (to current version):
 *   Kshitij Bansal, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An additional layer between commands and invoking them.
 */

#include "main/command_executor.h"

#ifndef __WIN32__
#  include <sys/resource.h>
#endif /* ! __WIN32__ */

#include <iomanip>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "main/main.h"
#include "smt/command.h"
#include "smt/solver_engine.h"

namespace cvc5 {
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

CommandExecutor::CommandExecutor(std::unique_ptr<api::Solver>& solver)
    : d_solver(solver),
      d_symman(new SymbolManager(d_solver.get())),
      d_result()
{
}
CommandExecutor::~CommandExecutor()
{
}

void CommandExecutor::storeOptionsAsOriginal()
{
  d_solver->d_originalOptions->copyValues(d_solver->d_slv->getOptions());
}

void CommandExecutor::printStatistics(std::ostream& out) const
{
  if (d_solver->getOptionInfo("stats").boolValue())
  {
    const auto& stats = d_solver->getStatistics();
    auto it = stats.begin(d_solver->getOptionInfo("stats-expert").boolValue(),
                          d_solver->getOptionInfo("stats-all").boolValue());
    for (; it != stats.end(); ++it)
    {
      out << it->first << " = " << it->second << std::endl;
    }
  }
}

void CommandExecutor::printStatisticsSafe(int fd) const
{
  if (d_solver->getOptionInfo("stats").boolValue())
  {
    d_solver->printStatisticsSafe(fd);
  }
}

bool CommandExecutor::doCommand(Command* cmd)
{
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
    if (d_solver->getOptionInfo("verbosity").intValue() > 2)
    {
      d_solver->getDriverOptions().out() << "Invoking: " << *cmd << std::endl;
    }

    return doCommandSingleton(cmd);
  }
}

void CommandExecutor::reset()
{
  printStatistics(d_solver->getDriverOptions().err());
  Command::resetSolver(d_solver.get());
}

bool CommandExecutor::doCommandSingleton(Command* cmd)
{
  bool status = solverInvoke(
      d_solver.get(), d_symman.get(), cmd, d_solver->getDriverOptions().out());

  api::Result res;
  const CheckSatCommand* cs = dynamic_cast<const CheckSatCommand*>(cmd);
  if(cs != nullptr) {
    d_result = res = cs->getResult();
  }
  const CheckSatAssumingCommand* csa =
      dynamic_cast<const CheckSatAssumingCommand*>(cmd);
  if (csa != nullptr)
  {
    d_result = res = csa->getResult();
  }
  const QueryCommand* q = dynamic_cast<const QueryCommand*>(cmd);
  if(q != nullptr) {
    d_result = res = q->getResult();
  }

  bool isResultUnsat = res.isUnsat() || res.isEntailed();
  bool isResultSat = res.isSat() || res.isNotEntailed();

  // dump the model/proof/unsat core if option is set
  if (status) {
    std::vector<std::unique_ptr<Command> > getterCommands;
    if (d_solver->getOptionInfo("dump-models").boolValue()
        && (isResultSat
            || (res.isSatUnknown()
                && res.getUnknownExplanation() == api::Result::INCOMPLETE)))
    {
      getterCommands.emplace_back(new GetModelCommand());
    }
    if (d_solver->getOptionInfo("dump-proofs").boolValue() && isResultUnsat)
    {
      getterCommands.emplace_back(new GetProofCommand());
    }

    if ((d_solver->getOptionInfo("dump-instantiations").boolValue()
         || d_solver->getOptionInfo("dump-instantiations-debug").boolValue())
        && GetInstantiationsCommand::isEnabled(d_solver.get(), res))
    {
      getterCommands.emplace_back(new GetInstantiationsCommand());
    }

    if (d_solver->getOptionInfo("dump-unsat-cores").boolValue()
        && isResultUnsat)
    {
      getterCommands.emplace_back(new GetUnsatCoreCommand());
    }

    if (d_solver->getOptionInfo("dump-difficulty").boolValue()
        && (isResultUnsat || isResultSat || res.isSatUnknown()))
    {
      getterCommands.emplace_back(new GetDifficultyCommand());
    }

    if (!getterCommands.empty()) {
      // set no time limit during dumping if applicable
      if (d_solver->getOptionInfo("force-no-limit-cpu-while-dump").boolValue())
      {
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

bool solverInvoke(api::Solver* solver,
                  SymbolManager* sm,
                  Command* cmd,
                  std::ostream& out)
{
  // print output for -o raw-benchmark
  if (solver->isOutputOn("raw-benchmark"))
  {
    cmd->toStream(solver->getOutput("raw-benchmark"));
  }

  // In parse-only mode, we do not invoke any of the commands except define-fun
  // commands. We invoke define-fun commands because they add function names
  // to the symbol table.
  if (solver->getOptionInfo("parse-only").boolValue()
      && dynamic_cast<SetBenchmarkLogicCommand*>(cmd) == nullptr
      && dynamic_cast<DefineFunctionCommand*>(cmd) == nullptr
      && dynamic_cast<ResetCommand*>(cmd) == nullptr)
  {
    return true;
  }

  cmd->invoke(solver, sm, out);
  return !cmd->fail();
}

void CommandExecutor::flushOutputStreams() {
  printStatistics(d_solver->getDriverOptions().err());

  // make sure out and err streams are flushed too
  d_solver->getDriverOptions().out() << std::flush;
  d_solver->getDriverOptions().err() << std::flush;
}

}  // namespace main
}  // namespace cvc5
