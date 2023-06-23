/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An additional layer between commands and invoking them.
 */

#ifndef CVC5__MAIN__COMMAND_EXECUTOR_H
#define CVC5__MAIN__COMMAND_EXECUTOR_H

#include <cvc5/cvc5.h>

#include <iosfwd>
#include <string>

#include "parser/api/cpp/symbol_manager.h"

namespace cvc5 {

namespace parser {
class Command;
}

namespace main {

class CommandExecutor
{
 protected:
  /**
   * The solver object, which is allocated by this class and is used for
   * executing most commands (e.g. check-sat).
   */
  std::unique_ptr<cvc5::Solver>& d_solver;
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
  std::unique_ptr<parser::SymbolManager> d_symman;

  cvc5::Result d_result;

  /** Cache option value of parse-only option. */
  bool d_parseOnly;

 public:
  CommandExecutor(std::unique_ptr<cvc5::Solver>& solver);

  virtual ~CommandExecutor();

  /**
   * Executes a command. Recursively handles if cmd is a command
   * sequence.  Eventually uses doCommandSingleton (which can be
   * overridden by a derived class).
   */
  bool doCommand(cvc5::parser::Command* cmd);

  bool doCommand(std::unique_ptr<cvc5::parser::Command>& cmd)
  {
    return doCommand(cmd.get());
  }

  /** Get a pointer to the solver object owned by this CommandExecutor. */
  cvc5::Solver* getSolver() { return d_solver.get(); }

  /** Get a pointer to the symbol manager owned by this CommandExecutor */
  parser::SymbolManager* getSymbolManager() { return d_symman.get(); }

  cvc5::Result getResult() const { return d_result; }
  void reset();

  /** Store the current options as the original options */
  void storeOptionsAsOriginal();

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
 virtual bool doCommandSingleton(cvc5::parser::Command* cmd);

private:
  CommandExecutor();

  bool solverInvoke(cvc5::Solver* solver,
                    parser::SymbolManager* sm,
                    parser::Command* cmd,
                    std::ostream& out);
}; /* class CommandExecutor */


}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__COMMAND_EXECUTOR_H */
