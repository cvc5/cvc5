/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mathias Preiner, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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

namespace internal {

class InteractiveShell
{
 public:
  using CmdSeq = std::vector<std::unique_ptr<cvc5::parser::Command>>;

  InteractiveShell(Solver* solver,
                   cvc5::parser::SymbolManager* sm,
                   std::istream& in,
                   std::ostream& out,
                   bool isInteractive = true);

  /**
   * Close out the interactive session.
   */
  ~InteractiveShell();

  /**
   * Read a list of commands from the interactive shell. This will read as
   * many lines as necessary to parse at least one well-formed command.
   */
  std::optional<CmdSeq> readCommand();

  /**
   * Return the internal parser being used.
   */
  cvc5::parser::InputParser* getParser() { return d_parser.get(); }

 private:
  Solver* d_solver;
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
