/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  /**
   * Constructor.
   * @param tm The associated term manager instance.
   */
  SymbolManager(cvc5::TermManager& tm);
  /**
   * Constructor.
   * @param slv The solver instance.
   * @warning This constructor is deprecated and replaced by
   *          `SymbolManager::SymbolManager(TermManager&)`. It will be removed
   *          in a future release.
   */
  [[deprecated("Use SymbolManager::SymbolManager(TermManager&) instead")]]
  SymbolManager(cvc5::Solver* slv);

  /**
   * Destructor.
   */
  ~SymbolManager();

  /**
   * Determine if the logic of this symbol manager has been set.
   * @return True if the logic has been set.
   */
  bool isLogicSet() const;
  /**
   * Get the logic configured for this symbol manager.
   * @note Asserts isLogicSet().
   * @return The configured logic.
   */
  const std::string& getLogic() const;

  /**
   * Get the list of sorts that have been declared via `declare-sort` commands.
   * These are the sorts that are printed as part of a response to a
   * `get-model` command.
   *
   * @return The declared sorts.
   */
  std::vector<Sort> getDeclaredSorts() const;

  /**
   * Get the list of terms that have been declared via `declare-fun` and
   * `declare-const`. These are the terms that are printed in response to a
   * `get-model` command.
   *
   * @return The declared terms.
   */
  std::vector<Term> getDeclaredTerms() const;

  /**
   * Get a mapping from terms to names that have been given to them via the
   * :named attribute.
   *
   * @return A map of the named terms to their names.
   */
  std::map<Term, std::string> getNamedTerms() const;

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
   * Get a string representation of this command.
   * @return The string representation.
   */
  std::string toString() const;

  /**
   * Get the name for this command, e.g., "assert".
   * @return The name of this command.
   */
  std::string getCommandName() const;

  /**
   * Determine if this command is null.
   * @return True if this command is null.
   */
  bool isNull() const;

 private:
  /**
   * Constructor.
   * @param cmd The internal command that is to be wrapped by this command.
   * @return The Command.
   */
  Command(std::shared_ptr<Cmd> cmd);
  /** The implementation of the symbol manager */
  std::shared_ptr<Cmd> d_cmd;
}; /* class Command */

 CVC5_EXPORT std::ostream& operator<<(std::ostream&, const Command&);

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first configured via,
 * e.g., `InputParser::setFileInput()`, `InputParser::setStreamInput()`,
 * `InputParser::setStringInput()` or
 * `InputParser::setIncrementalStringInput()` and
 * `InputParser::appendIncrementalStringInput()`.
 * Then, functions `InputParser::nextCommand()` and
 * `InputParser::nextExpression()` can be invoked to parse the input.
 *
 * The input parser interacts with a symbol manager, which determines which
 * symbols are defined in the current context, based on the background logic
 * and user-defined symbols. If no symbol manager is provided, then the
 * input parser will construct (an initially empty) one.
 *
 * If provided, the symbol manager must have a logic that is compatible
 * with the provided solver. That is, if both the solver and symbol
 * manager have their logics set (`SymbolManager::isLogicSet()` and
 * `Solver::isLogicSet()`), then their logics must be the same.
 *
 * Upon setting an input source, if either the solver (resp. symbol manager)
 * has its logic set, then the symbol manager (resp. solver) is set to use that
 * logic, if its logic is not already set.
 */
class CVC5_EXPORT InputParser
{
  friend class internal::InteractiveShell;

 public:
  /**
   * Construct an input parser
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   * @param sm The symbol manager, which contains a symbol table that maps
   *           symbols to terms and sorts. Must have a logic that is compatible
   *           with the solver.
   */
  InputParser(Solver* solver, SymbolManager* sm);
  /**
   * Construct an input parser with an initially empty symbol manager.
   * @param solver The solver (e.g. for constructing terms and sorts)
   */
  InputParser(Solver* solver);

  /**
   * Get the associated solver instance of this input parser.
   * @return The solver instance.
   */
  Solver* getSolver();
  /**
   * Get the associated symbol manager of this input parser.
   * @return The associated symbol manager.
   */
  SymbolManager* getSymbolManager();
  /**
   * Configure given file as input.
   * @param lang     The input language (e.g.,
   *                 `modes::InputLanguage::SMT_LIB_2_6`).
   * @param filename The name of the file to configure.
   */
  void setFileInput(modes::InputLanguage lang, const std::string& filename);

  /**
   * Configure given stream as input.
   * @param lang  The input language.
   * @param input The input stream.
   * @param name  The name of the stream, for use in error messages.
   */
  void setStreamInput(modes::InputLanguage lang,
                      std::istream& input,
                      const std::string& name);

  /**
   * Configure a given concrete input string as the input to this parser.
   * @param lang  The input language of the input string.
   * @param input The input string.
   * @param name  The name to use as input stream name for error messages.
   */
  void setStringInput(modes::InputLanguage lang,
                      const std::string& input,
                      const std::string& name);

  /**
   * Configure that we will be feeding strings to this parser via
   * `appendIncrementalStringInput()` below.
   *
   * @param lang the input language
   * @param name the name of the stream, for use in error messages
   */
  void setIncrementalStringInput(modes::InputLanguage lang,
                                 const std::string& name);
  /**
   * Append string to the input being parsed by this parser. Should be
   * called after calling `setIncrementalStringInput()`.
   * @param input The input string
   */
  void appendIncrementalStringInput(const std::string& input);

  /**
   * Parse and return the next command. Will initialize the logic to "ALL"
   * or the forced logic if no logic is set prior to this point and a command
   * is read that requires initializing the logic.
   *
   * @return The parsed command. This is the null command if no command was
   *         read.
   */
  Command nextCommand();

  /**
   * Parse and return the next term. Requires setting the logic prior
   * to this point.
   * @return The parsed term.
   */
  Term nextTerm();

  /**
   * Is this parser done reading input?
   * @return True if parser is done reading input.
   */
  bool done() const;

 private:
  /**
   * Set the input to the given concrete input string, without allocating a new parser.
   */
  void setStringInputInternal(const std::string& input,
                              const std::string& name);
  /**
   * Set the input to incremental string input.
   * @param lang The input language.
   * @param name The name of the stream, for use in error messages.
   */
  void setIncrementalStringInputInternal(modes::InputLanguage lang,
                                         const std::string& name);
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
  /** A stringstream, for incremental string inputs */
  std::stringstream d_istringStream;
  /** Are we initialized to use the above string stream? */
  bool d_usingIStringStream;
  /** The last language argument passed to setIncrementalStringInput(). */
  modes::InputLanguage d_istringLang;
  /** The last name argument passed to setIncrementalStringInput(). */
  std::string d_istringName;
  /** The parser */
  std::shared_ptr<Parser> d_parser;
};

/**
 * Base class for all Parser exceptions.
 * If thrown, API objects can still be used
 */
class CVC5_EXPORT ParserException : public CVC5ApiException
{
 public:
  /** Default constructor */
  ParserException();
  /**
   * Construct with message from a string.
   * @param msg The error message.
   */
  ParserException(const std::string& msg);
  /**
   * Construct with message from a C string.
   * @param msg The error message.
   */
  ParserException(const char* msg);
  /**
   * Construct with message from a string.
   * @param msg The error message.
   * @param filename name of the file.
   * @param line The error line number.
   * @param column The error column number.
   */
  ParserException(const std::string& msg,
                  const std::string& filename,
                  unsigned long line,
                  unsigned long column);

  /**
   * Print error to output stream.
   * @param os The output stream to write the error on.
   */
  void toStream(std::ostream& os) const override;

  /**
   * @return The file name.
   */
  std::string getFilename() const;

  /**
   * @return The line number of the parsing error.
   */
  unsigned long getLine() const;
  /**
   * @return The column number of the parsing error.
   */
  unsigned long getColumn() const;

 protected:
  /** The file name of the parsing error. */
  std::string d_filename;
  /** The line number of the parsing error. */
  unsigned long d_line;
  /** The column number of the parsing error. */
  unsigned long d_column;
}; /* class ParserException */

/**
 * An end of file exception.
 * If thrown, API objects can still be used
 */
class CVC5_EXPORT ParserEndOfFileException : public ParserException
{
 public:
  /** default constructor */
  ParserEndOfFileException();
  /**
   * Construct with message from a string.
   * @param msg The error message.
   */
  ParserEndOfFileException(const std::string& msg);
  /**
   * Construct with message from a C string.
   * @param msg The error message.
   */
  ParserEndOfFileException(const char* msg);
  /**
   * Construct with message from a string.
   * @param msg The error message.
   * @param filename The name of the file.
   * @param line The error line number.
   * @param column The error column number.
   */
  ParserEndOfFileException(const std::string& msg,
                           const std::string& filename,
                           unsigned long line,
                           unsigned long column);

}; /* class ParserEndOfFileException */

}  // namespace parser
}  // namespace cvc5

#endif
