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

#include "parser/language.h"
#include "parser/parser_state.h"

namespace CVC4 {

// Forward declarations
class Expr;
class Command;
class ExprManager;
class SmtEngine;
class Options;

namespace parser {

/**
 * The global pointer to ParserTemp.  Each instance of class Parser sets this pointer
 * before any calls to the lexer.  We do it this way because flex and bison use global
 * vars, and we want each Parser object to appear independent.
 */
extern ParserState CVC4_PUBLIC *_global_parser_state;

/**
 * The parser.
 */
class CVC4_PUBLIC Parser {
 private:

  /** Internal parser state we are keeping */
  //ParserState* d_data;

  /** Initialize the parser */
  void initParser();

  /** Remove the parser components */
  void deleteParser();

  Language d_lang;
  std::istream &d_in;
  Options *d_opts;

 public:

  /**
   * Constructor for parsing out of a file.
   * @param em the expression manager to use
   * @param lang the language syntax to use
   * @param file_name the file to parse
   */
  Parser(SmtEngine* smt, ExprManager* em, Language lang, std::istream& in, Options* opts) :
    d_lang(lang), d_in(in), d_opts(opts) {
    _global_parser_state = new ParserState(smt, em);
    _global_parser_state->setInputStream(in);
  }

  /**
   * Destructor.
   */
  ~Parser();

  /** Parse a command */
  Command* parseNextCommand(bool verbose = false);

  /** Parse an expression of the stream */
  Expr parseNextExpression();

  // Check if we are done (end of input has been reached)
  bool done() const;

  // The same check can be done by using the class Parser's value as a Boolean
  operator bool() const { return done(); }

  /** Prints the location to the output stream */
  void printLocation(std::ostream& out) const;

  /** Reset any local data */
  void reset();
}; // end of class Parser

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
