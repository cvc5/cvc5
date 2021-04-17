/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Gereon Kremer
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

#ifndef CVC5__MAIN__COMMAND_EXECUTOR_H
#define CVC5__MAIN__COMMAND_EXECUTOR_H

#include <iosfwd>
#include <string>

#include "api/cpp/cvc5.h"
#include "expr/symbol_manager.h"
#include "options/options.h"

namespace cvc5 {

class Command;

namespace smt {
class SmtEngine;
}

namespace main {

class CommandExecutor
{
 protected:
  /**
   * The solver object, which is allocated by this class and is used for
   * executing most commands (e.g. check-sat).
   */
  std::unique_ptr<api::Solver> d_solver;
  /**
   * The symbol manager, which is allocated by this class. This manages
   * all things related to definitions of symbols and their impact on behaviors
   * for commands (e.g. get-unsat-core, get-model, get-assignment), as well
   * as tracking expression names. Note the symbol manager is independent from
   * the parser, which uses this symbol manager given a text input.
   *
   * Certain commands (e.g. reset-assertions) have a specific impact on the
   * symbol manager.
   */
  std::unique_ptr<SymbolManager> d_symman;
  Options& d_options;
  api::Result d_result;

 public:
  CommandExecutor(Options& options);

  virtual ~CommandExecutor();

  /**
   * Executes a command. Recursively handles if cmd is a command
   * sequence.  Eventually uses doCommandSingleton (which can be
   * overridden by a derived class).
   */
  bool doCommand(cvc5::Command* cmd);

  bool doCommand(std::unique_ptr<cvc5::Command>& cmd)
  {
    return doCommand(cmd.get());
  }

  /** Get a pointer to the solver object owned by this CommandExecutor. */
  api::Solver* getSolver() { return d_solver.get(); }

  /** Get a pointer to the symbol manager owned by this CommandExecutor */
  SymbolManager* getSymbolManager() { return d_symman.get(); }

  api::Result getResult() const { return d_result; }
  void reset();

  SmtEngine* getSmtEngine() const { return d_solver->getSmtEngine(); }

  /**
   * Prints statistics to an output stream.
   * Checks whether statistics should be printed according to the options.
   * Thus, this method can always be called without checking the options.
   */
  virtual void printStatistics(std::ostream& out) const;

  /**
   * Safely prints statistics to a file descriptor.
   * This method is safe to be used within a signal handler.
   * Checks whether statistics should be printed according to the options.
   * Thus, this method can always be called without checking the options.
   */
  void printStatisticsSafe(int fd) const;

  void flushOutputStreams();

protected:
  /** Executes treating cmd as a singleton */
 virtual bool doCommandSingleton(cvc5::Command* cmd);

private:
  CommandExecutor();

}; /* class CommandExecutor */

bool solverInvoke(api::Solver* solver,
                  SymbolManager* sm,
                  Command* cmd,
                  std::ostream* out);

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__COMMAND_EXECUTOR_H */
