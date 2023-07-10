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
 * Base class for  parsing.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_H
#define CVC5__PARSER__PARSER_H

#include <cvc5/cvc5.h>

#include <list>
#include <memory>

#include "parser/input.h"
#include "parser/parser_state.h"

namespace cvc5 {
namespace parser {

class Command;
class SymbolManager;
class Lexer;

/**
 * A parser that uses the Lexer for lexing. It is used as a callback
 * for error reporting. Its main methods are those that set up the input,
 * nextCommand for parsing commands and nextExpression for parsing terms.
 */
class Parser : public ParserStateCallback
{
 public:
  Parser(Solver* solver, SymbolManager* sm);
  virtual ~Parser() {}
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

  /** Is this parser done reading input? */
  bool done() const;

  /** Issue a warning to the user. */
  void warning(const std::string& msg) override;
  /** Raise a parse error with the given message. */
  void parseError(const std::string& msg) override;
  /** Unexpectedly encountered an EOF */
  void unexpectedEOF(const std::string& msg) override;

  /** make flex parser from language string */
  static std::unique_ptr<Parser> mkParser(const std::string& lang,
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
  Lexer* d_lex;
  /** The flex input */
  std::unique_ptr<Input> d_flexInput;
  /** Are we done */
  bool d_done;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_H */
