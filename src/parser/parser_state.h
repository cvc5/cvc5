/*********************                                           -*- C++ -*-  */
/** parser_state.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Extra state of the parser shared by the lexer and parser.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_PARSER_STATE_H
#define __CVC4_PARSER_STATE_H

#include <iostream>
#include <sstream>
#include "cvc4_expr.h"
#include "exception.h"

namespace CVC4 {

class ValidityChecker;

class ParserState {
private:
  // Counter for uniqueID of bound variables
  int d_uid;
  // The main prompt when running interactive
  std::string prompt1;
  // The interactive prompt in the middle of a multi-line command
  std::string prompt2;
  // The currently used prompt
  std::string prompt;
public:
  ValidityChecker* vc;
  std::istream* is;
  // The current input line
  int lineNum;
  // File name
  std::string fileName;
  // The last parsed Expr
  Expr expr;
  // Whether we are done or not
  bool done;
  // Whether we are running interactive
  bool interactive;
  // Whether arrays are enabled for smt-lib format
  bool arrFlag;
  // Whether bit-vectors are enabled for smt-lib format
  bool bvFlag;
  // Size of bit-vectors for smt-lib format
  int bvSize;
  // Did we encounter a formula query (smtlib)
  bool queryParsed;
  // Default constructor
  ParserState() : d_uid(0),
                  prompt1("CVC> "),
                  prompt2("- "),
                  prompt("CVC> "),
                  vc(0),
                  is(0),
                  lineNum(1),
                  fileName(),
                  expr(Expr::null()),
                  done(false),
                  interactive(false),
                  arrFlag(false),
                  bvFlag(false),
                  bvSize(0),
                  queryParsed(false) { }
  // Parser error handling (implemented in parser.cpp)
  int error(const std::string& s);
  // Get the next uniqueID as a string
  std::string uniqueID() {
    std::ostringstream ss;
    ss << d_uid++;
    return ss.str();
  }
  // Get the current prompt
  std::string getPrompt() { return prompt; }
  // Set the prompt to the main one
  void setPrompt1() { prompt = prompt1; }
  // Set the prompt to the secondary one
  void setPrompt2() { prompt = prompt2; }
};

} /* CVC4 namespace */

#endif /* __CVC4_PARSER_STATE_H */
