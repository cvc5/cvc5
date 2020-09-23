/*********************                                                        */
/*! \file command_executor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An additional layer between commands and invoking them.
 **/

#ifndef CVC4__MAIN__COMMAND_EXECUTOR_H
#define CVC4__MAIN__COMMAND_EXECUTOR_H

#include <iosfwd>
#include <string>

#include "api/cvc4cpp.h"
#include "expr/expr_manager.h"
#include "options/options.h"
#include "smt/smt_engine.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class Command;

namespace api {
class Solver;
}

namespace main {

class CommandExecutor
{
 private:
  std::string d_lastStatistics;

 protected:
  std::unique_ptr<api::Solver> d_solver;
  SmtEngine* d_smtEngine;
  Options& d_options;
  StatisticsRegistry d_stats;
  api::Result d_result;

 public:
  CommandExecutor(Options& options);

  virtual ~CommandExecutor()
  {
  }

  /**
   * Executes a command. Recursively handles if cmd is a command
   * sequence.  Eventually uses doCommandSingleton (which can be
   * overridden by a derived class).
   */
  bool doCommand(CVC4::Command* cmd);

  bool doCommand(std::unique_ptr<CVC4::Command>& cmd) {
    return doCommand(cmd.get());
  }

  /** Get a pointer to the solver object owned by this CommandExecutor. */
  api::Solver* getSolver() { return d_solver.get(); }

  api::Result getResult() const { return d_result; }
  void reset();

  StatisticsRegistry& getStatisticsRegistry() {
    return d_stats;
  }

  SmtEngine* getSmtEngine() { return d_smtEngine; }

  /**
   * Flushes statistics to a file descriptor.
   */
  virtual void flushStatistics(std::ostream& out) const;

  /**
   * Flushes statistics to a file descriptor.
   * Safe to use in a signal handler.
   */
  void safeFlushStatistics(int fd) const;

  static void printStatsFilterZeros(std::ostream& out,
                                    const std::string& statsString);

  void flushOutputStreams();

protected:
  /** Executes treating cmd as a singleton */
  virtual bool doCommandSingleton(CVC4::Command* cmd);

private:
  CommandExecutor();

}; /* class CommandExecutor */

bool solverInvoke(api::Solver* solver, Command* cmd, std::ostream* out);

}/* CVC4::main namespace */
}/* CVC4 namespace */

#endif  /* CVC4__MAIN__COMMAND_EXECUTOR_H */
