/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Interactive shell for cvc5.
 */

#ifndef CVC5__INTERACTIVE_SHELL_H
#define CVC5__INTERACTIVE_SHELL_H

#include <iosfwd>
#include <memory>
#include <optional>
#include <string>
#include <vector>

namespace cvc5 {

class Solver;

namespace parser {
class Command;
class InputParser;
class SymbolManager;
}  // namespace parser

namespace main {
class CommandExecutor;
}

namespace internal {

class InteractiveShell
{
 public:
  InteractiveShell(main::CommandExecutor* cexec,
                   std::istream& in,
                   std::ostream& out,
                   bool isInteractive = true);

  /**
   * Close out the interactive session.
   */
  ~InteractiveShell();

  /**
   * Read a list of commands from the interactive shell. This will read as
   * many lines as necessary to parse at least one well-formed command,
   * and execute them.
   */
  bool readAndExecCommands();

  /**
   * Return the internal parser being used.
   */
  cvc5::parser::InputParser* getParser() { return d_parser.get(); }

 private:
  main::CommandExecutor* d_cexec;
  Solver* d_solver;
  cvc5::parser::SymbolManager* d_symman;
  std::istream& d_in;
  std::ostream& d_out;
  std::unique_ptr<cvc5::parser::InputParser> d_parser;
  /** Only true if we are actually asking the user for input */
  bool d_isInteractive;
  bool d_quit;
  bool d_usingEditline;

  std::string d_historyFilename;

  static const std::string INPUT_FILENAME;
  static const unsigned s_historyLimit = 500;
}; /* class InteractiveShell */

}  // namespace internal
}  // namespace cvc5

#endif /* CVC5__INTERACTIVE_SHELL_H */
