/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The interface for parsing an input with a parser.
 */

#include <cvc5/cvc5_export.h>

#ifndef CVC5__API__CVC5_PARSER_H
#define CVC5__API__CVC5_PARSER_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_types.h>

#include <memory>

namespace cvc5 {

namespace internal {
class InteractiveShell;
}
namespace main {
class CommandExecutor;
class ExecutionContext;
}  // namespace main

namespace parser {

class Command;
class Cmd;
class InputParser;
class Parser;
class SymbolManager;
class CommandStatus;
class SymManager;

/**
 * Symbol manager. Internally, this class manages a symbol table and other
 * meta-information pertaining to SMT2 file inputs (e.g. named assertions,
 * declared functions, etc.).
 *
 * A symbol manager can be modified by invoking commands, see Command::invoke.
 *
 * A symbol manager can be provided when constructing an InputParser, in which
 * case that InputParser has symbols of this symbol manager preloaded.
 *
 * The symbol manager's interface is otherwise not publicly available.
 */
class CVC5_EXPORT SymbolManager
{
  friend class InputParser;
  friend class Command;
  friend class internal::InteractiveShell;
  friend class main::CommandExecutor;

 public:
  SymbolManager(cvc5::Solver* s);
  ~SymbolManager();

  /**
   * @return true if the logic of this symbol manager has been set.
   */
  bool isLogicSet() const;
  /**
   * @note Asserts isLogicSet().
   *
   * @return the logic used by this symbol manager
   */
  const std::string& getLogic() const;

 private:
  /** Get the underlying implementation */
  SymManager* toSymManager();
  /** The implementation of the symbol manager */
  std::shared_ptr<SymManager> d_sm;
};

/**
 * Encapsulation of a command.
 *
 * Commands are constructed by the input parser and can be invoked on
 * the solver and symbol manager.
 */
class CVC5_EXPORT Command
{
  friend class InputParser;
  friend class main::CommandExecutor;
  friend class internal::InteractiveShell;
  friend class main::ExecutionContext;

 public:
  Command();

  /**
   * Invoke the command on the solver and symbol manager sm, prints the result
   * to output stream out.
   *
   * @param solver The solver to invoke the command on.
   * @param sm The symbol manager to invoke the command on.
   * @param out The output stream to write the result of the command on.
   */
  void invoke(cvc5::Solver* solver,
              parser::SymbolManager* sm,
              std::ostream& out);

  /**
   * @return A string representation of this result.
   */
  std::string toString() const;

  /**
   * Get the name for this command, e.g. "assert".
   *
   * @return The name of this command.
   */
  std::string getCommandName() const;

  /**
   * @return True if this command is null.
   */
  bool isNull() const;

 private:
  /**
   * Constructor.
   * @param n The internal command that is to be wrapped by this command.
   * @return The Command.
   */
  Command(std::shared_ptr<Cmd> cmd);
  /** Return the internal representation */
  Cmd* toCmd();
  /** The implementation of the symbol manager */
  std::shared_ptr<Cmd> d_cmd;
}; /* class Command */

std::ostream& operator<<(std::ostream&, const Command&) CVC5_EXPORT;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via e.g.
 * setFileInput, setStreamInput, or setIncrementalStringInput and
 * appendIncrementalStringInput. Then, the methods nextCommand and
 * nextExpression can be invoked to parse the input.
 *
 * The input parser interacts with a symbol manager, which determines which
 * symbols are defined in the current context, based on the background logic
 * and user-defined symbols. If no symbol manager is provided, then the
 * input parser will construct (an initially empty) one.
 *
 * If provided, the symbol manager must have a logic that is compatible
 * with the provided solver. That is, if both the solver and symbol
 * manager have their logics set (SymbolManager::isLogicSet and
 * Solver::isLogicSet), then their logics must be the same.
 *
 * Upon setting an input source, if either the solver (resp. symbol
 * manager) has its logic set, then the symbol manager (resp. solver) is set to
 * use that logic, if its logic is not already set.
 */
class CVC5_EXPORT InputParser
{
 public:
  /**
   * Construct an input parser
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   * @param sm The symbol manager, which contains a symbol table that maps
   * symbols to terms and sorts. Must have a logic that is compatible
   * with the solver.
   */
  InputParser(Solver* solver, SymbolManager* sm);
  /**
   * Construct an input parser with an initially empty symbol manager.
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   */
  InputParser(Solver* solver);

  /**
   * @return The underlying solver of this input parser
   */
  Solver* getSolver();
  /**
   * @return The underlying symbol manager of this input parser
   */
  SymbolManager* getSymbolManager();
  /** Set the input for the given file.
   *
   * @param lang the input language (e.g. modes::InputLanguage::SMT_LIB_2_6)
   * @param filename the input filename
   */
  void setFileInput(modes::InputLanguage lang, const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  void setStreamInput(modes::InputLanguage lang,
                      std::istream& input,
                      const std::string& name);

  /**
   * Set that we will be feeding strings to this parser via
   * appendIncrementalStringInput below.
   *
   * @param lang the input language
   * @param name the name of the stream, for use in error messages
   */
  void setIncrementalStringInput(modes::InputLanguage lang,
                                 const std::string& name);
  /**
   * Append string to the input being parsed by this parser. Should be
   * called after calling setIncrementalStringInput and only after the
   * previous string (if one was provided) is finished being parsed.
   *
   * @param input The input string
   */
  void appendIncrementalStringInput(const std::string& input);

  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   *
   * @return The parsed command. This is the null command if no command was
   * read.
   */
  Command nextCommand();

  /**
   * Parse and return the next term. Requires setting the logic prior
   * to this point.
   */
  Term nextTerm();

  /** Is this parser done reading input? */
  bool done() const;

 private:
  /** Initialize this input parser, called during construction */
  void initialize();
  /**
   * Initialize the internal parser, called immediately after d_parser
   * is constructed.
   */
  void initializeInternal();
  /** Solver */
  Solver* d_solver;
  /** The allocated symbol manager */
  std::unique_ptr<SymbolManager> d_allocSm;
  /** Symbol manager */
  SymbolManager* d_sm;
  /** Incremental string input language */
  modes::InputLanguage d_istringLang;
  /** Incremental string name */
  std::string d_istringName;
  /** The parser */
  std::shared_ptr<Parser> d_parser;
};

}  // namespace parser
}  // namespace cvc5

#endif
