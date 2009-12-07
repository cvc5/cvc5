/*********************                                           -*- C++ -*-  */
/** parser.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser abstraction.
 **/

#ifndef __CVC4__PARSER__PARSER_H
#define __CVC4__PARSER__PARSER_H

#include <string>
#include <iostream>
#include <fstream>
#include "cvc4_config.h"
#include "parser_exception.h"

namespace CVC4 {

// Forward declarations
class Expr;
class Command;
class ExprManager;

namespace parser {

class AntlrSmtLexer;
class AntlrSmtParser;
class AntlrCvcLexer;
class AntlrCvcParser;

/**
 * The parser.
 */
class CVC4_PUBLIC Parser {

public:

  /**
   * Construct the parser that uses the given expression manager.
   * @param em the expression manager.
   */
  Parser(ExprManager* em);

  /**
   * Destructor.
   */
  virtual ~Parser() {
  }

  /**
   * Parse the next command of the input
   */
  virtual Command* parseNextCommand() throw (ParserException) = 0;

  /**
   * Parse the next expression of the stream
   */
  virtual Expr parseNextExpression() throw (ParserException) = 0;

  /**
   * Check if we are done -- either the end of input has been reached.
   */
  bool done() const;

protected:

  /** Sets the done flag */
  void setDone(bool done = true);

  /** Expression manager the parser will be using */
  ExprManager* d_expr_manager;

  /** Are we done */
  bool d_done;

}; // end of class Parser

class CVC4_PUBLIC SmtParser : public Parser {

public:

  /**
   * Construct the parser that uses the given expression manager and parses
   * from the given input stream.
   * @param em the expression manager to use
   * @param input the input stream to parse
   */
  SmtParser(ExprManager* em, std::istream& input);

  /**
   * Construct the parser that uses the given expression manager and parses
   * from the file.
   * @param em the expression manager to use
   * @param file_name the file to parse
   */
  SmtParser(ExprManager* em, const char* file_name);

  /**
   * Destructor.
   */
  ~SmtParser();

  /**
   * Parses the next command. By default, the SMTLIB parser produces one
   * CommandSequence command. If parsing is successful, we should be done
   * after the first call to this command.
   * @return the CommandSequence command that includes the whole benchmark
   */
  Command* parseNextCommand() throw (ParserException);

  /**
   * Parses the next complete expression of the stream.
   * @return the expression parsed
   */
  Expr parseNextExpression() throw (ParserException);

protected:

  /** The ANTLR smt lexer */
  AntlrSmtLexer* d_antlr_lexer;

  /** The ANTLR smt parser */
  AntlrSmtParser* d_antlr_parser;

  /** The file stream we might be using */
  std::ifstream d_input;
};

class CVC4_PUBLIC CvcParser : public Parser {

public:

  /**
   * Construct the parser that uses the given expression manager and parses
   * from the given input stream.
   * @param em the expression manager to use
   * @param input the input stream to parse
   */
  CvcParser(ExprManager* em, std::istream& input);

  /**
   * Construct the parser that uses the given expression manager and parses
   * from the file.
   * @param em the expression manager to use
   * @param file_name the file to parse
   */
  CvcParser(ExprManager* em, const char* file_name);

  /**
   * Destructor.
   */
  ~CvcParser();

  /**
   * Parses the next command. By default, the SMTLIB parser produces one
   * CommandSequence command. If parsing is successful, we should be done
   * after the first call to this command.
   * @return the CommandSequence command that includes the whole benchmark
   */
  Command* parseNextCommand() throw (ParserException);

  /**
   * Parses the next complete expression of the stream.
   * @return the expression parsed
   */
  Expr parseNextExpression() throw (ParserException);

protected:

  /** The ANTLR smt lexer */
  AntlrCvcLexer* d_antlr_lexer;

  /** The ANTLR smt parser */
  AntlrCvcParser* d_antlr_parser;

  /** The file stream we might be using */
  std::ifstream d_input;
};


}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
