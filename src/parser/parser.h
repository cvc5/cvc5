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

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
