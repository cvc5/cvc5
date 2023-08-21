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

#include <memory>

namespace cvc5 {
  
namespace main {
class CommandExecutor;
}
  
namespace internal {
class InteractiveShell;
}

namespace parser {

class Command;
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

 public:
  SymbolManager(cvc5::Solver* s);
  ~SymbolManager();
 private:
  /** Get the underlying implementation */
  SymManager* get();
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
  friend class main::CommandExecutor;
 public:
  Command();
  Command(const Command& cmd);

  virtual ~Command();

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
  virtual std::string getCommandName() const = 0;

  /**
   * Either the command hasn't run yet, or it completed successfully
   * (CommandSuccess, not CommandUnsupported or CommandFailure).
   *
   * @return Whether the command was successfully invoked.
   */
  bool ok() const;

  /**
   * The command completed in a failure state (CommandFailure, not
   * CommandSuccess or CommandUnsupported).
   *
   * @return Whether the command failed.
   */
  bool fail() const;

  /**
   * The command was ran but was interrupted due to resource limiting.
   *
   * @return Whether the command was interrupted.
   */
  bool interrupted() const;

 protected:
  virtual void toStream(std::ostream& out) const = 0;
  /**
   * This field contains a command status if the command has been
   * invoked, or NULL if it has not.  This field is either a
   * dynamically-allocated pointer, or it's a pointer to the singleton
   * CommandSuccess instance.  Doing so is somewhat asymmetric, but
   * it avoids the need to dynamically allocate memory in the common
   * case of a successful command.
   */
  const CommandStatus* d_commandStatus;
  /**
   * Print the result of running the command. This method is only called if the
   * command ran successfully.
   */
  virtual void printResult(cvc5::Solver* solver, std::ostream& out) const;
  /**
   * Reset the given solver in-place (keep the object at the same memory
   * location).
   */
  static void resetSolver(cvc5::Solver* solver);

  // These methods rely on Command being a friend of classes in the API.
  // Subclasses of command should use these methods for conversions,
  // which is currently necessary for e.g. printing commands.
  /** Helper to convert a Term to an internal internal::Node */
  static internal::Node termToNode(const cvc5::Term& term);
  /** Helper to convert a vector of Terms to internal Nodes. */
  static std::vector<internal::Node> termVectorToNodes(
      const std::vector<cvc5::Term>& terms);
  /** Helper to convert a Sort to an internal internal::TypeNode */
  static internal::TypeNode sortToTypeNode(const cvc5::Sort& sort);
  /** Helper to convert a vector of Sorts to internal TypeNodes. */
  static std::vector<internal::TypeNode> sortVectorToTypeNodes(
      const std::vector<cvc5::Sort>& sorts);
  /** Helper to convert a Grammar to an internal internal::TypeNode */
  static internal::TypeNode grammarToTypeNode(cvc5::Grammar* grammar);
  /**
   * Invoke the command on the solver and symbol manager sm.
   */
  virtual void invokeInternal(cvc5::Solver* solver, parser::SymManager* sm) = 0;
  /**
   * Same as above, and prints the result to output stream out.
   */
  virtual void invokeInternal(cvc5::Solver* solver,
                              parser::SymManager* sm,
                              std::ostream& out);
}; /* class Command */

std::ostream& operator<<(std::ostream&, const Command&) CVC5_EXPORT;
std::ostream& operator<<(std::ostream&, const Command*) CVC5_EXPORT;

/**
 * This class is the main interface for retrieving commands and expressions
 * from an input using a parser.
 *
 * After construction, it is expected that an input is first set via e.g.
 * setFileInput, setStreamInput, or setStringInput. Then, the methods
 * nextCommand and nextExpression can be invoked to parse the input.
 */
class CVC5_EXPORT InputParser
{
 public:
  /**
   * Construct an input parser
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   * @param sm The symbol manager, which contains a symbol table that maps
   * symbols to terms and sorts.
   */
  InputParser(Solver* solver, SymbolManager* sm);
  /**
   * Construct an input parser with an initially empty symbol manager.
   *
   * @param solver The solver (e.g. for constructing terms and sorts)
   */
  InputParser(Solver* solver);

  /** Get the underlying solver of this input parser */
  Solver* getSolver();
  /** Get the underlying symbol manager of this input parser */
  SymbolManager* getSymbolManager();
  /**
   * Set the logic to use. This determines which builtin symbols are included.
   *
   * @param name The name of the logic.
   */
  void setLogic(const std::string& name);
  /** Set the input for the given file.
   *
   * @param lang the input language
   * @param filename the input filename
   */
  void setFileInput(const std::string& lang, const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  void setStreamInput(const std::string& lang,
                      std::istream& input,
                      const std::string& name);

  /**
   * Set that we will be feeding strings to this parser via
   * appendIncrementalStringInput below.
   *
   * @param lang the input language
   * @param name the name of the stream, for use in error messages
   */
  void setIncrementalStringInput(const std::string& lang,
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
   */
  std::unique_ptr<Command> nextCommand();

  /**
   * Parse and return the next expression. Requires setting the logic prior
   * to this point.
   */
  Term nextExpression();

  /** Is this parser done reading input? */
  bool done() const;

 private:
  /** Initialize this input parser, called during construction */
  void initialize();
  /** Solver */
  Solver* d_solver;
  /** The allocated symbol manager */
  std::unique_ptr<SymbolManager> d_allocSm;
  /** Symbol manager */
  SymbolManager* d_sm;
  /** Incremental string input language */
  std::string d_istringLang;
  /** Incremental string name */
  std::string d_istringName;
  /** The parser */
  std::shared_ptr<Parser> d_fparser;
};

}  // namespace parser
}  // namespace cvc5

#endif
