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
 * Base class for Flex parsing.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__FLEX_PARSER_H
#define CVC5__PARSER__FLEX_PARSER_H

#include <cvc5/cvc5.h>

#include <list>
#include <memory>

#include "parser/flex_input.h"
#include "parser/parser.h"

namespace cvc5 {
namespace parser {

class Command;
class SymbolManager;
class FlexLexer;

/**
 * A parser that uses the FlexLexer for lexing. It is used as a callback
 * for error reporting. Its main methods are those that set up the input,
 * nextCommand for parsing commands and nextExpression for parsing terms.
 */
class FlexParser : public ParserStateCallback
{
 public:
  FlexParser(Solver* solver, SymbolManager* sm);
  virtual ~FlexParser() {}
  /**
   * Set the logic
   *
   * @param name The name of the logic.
   */
  virtual void setLogic(const std::string& name);
  /** Set the input for the given file.
   *
   * @param filename the input filename
   */
  void setFileInput(const std::string& filename);

  /** Set the input for the given stream.
   *
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  void setStreamInput(std::istream& input, const std::string& name);

  /** Set the input for the given string
   *
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  void setStringInput(const std::string& input, const std::string& name);

  /**
   * Parse and return the next command.
   */
  std::unique_ptr<Command> nextCommand();

  /** Parse and return the next expression. */
  Term nextExpression();

  /** Issue a warning to the user. */
  void warning(const std::string& msg) override;
  /** Raise a parse error with the given message. */
  void parseError(const std::string& msg) override;
  /** Unexpectedly encountered an EOF */
  void unexpectedEOF(const std::string& msg) override;
  /**
   * Preempt the next returned command with other ones; used to
   * support the :named attribute in SMT-LIBv2, which implicitly
   * inserts a new command before the current one. Also used in TPTP
   * because function and predicate symbols are implicitly declared.
   */
  void preemptCommand(std::unique_ptr<Command> cmd) override;

  /** make flex parser from language string */
  static std::unique_ptr<FlexParser> mkFlexParser(const std::string& lang,
                                                  Solver* solver,
                                                  SymbolManager* sm);

 protected:
  /** Initialize input */
  void initializeInput(const std::string& name);

  /** Sets the done flag */
  void setDone(bool done = true) { d_done = done; }
  /**
   * Parse and return the next command.
   * NOTE: currently memory management of commands is handled internally.
   */
  virtual std::unique_ptr<Command> parseNextCommand() = 0;

  /** Parse and return the next expression. */
  virtual Term parseNextExpression() = 0;
  /** Solver */
  Solver* d_solver;
  /** Symbol manager */
  SymbolManager* d_sm;
  /** The lexer we are using */
  FlexLexer* d_lex;
  /** The flex input */
  std::unique_ptr<FlexInput> d_flexInput;
  /**
   * "Preemption commands": extra commands implied by subterms that
   * should be issued before the currently-being-parsed command is
   * issued.  Used to support SMT-LIBv2 ":named" attribute on terms.
   *
   * Owns the memory of the Commands in the queue.
   */
  std::list<std::unique_ptr<Command>> d_commandQueue;
  /** Are we done */
  bool d_done;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
