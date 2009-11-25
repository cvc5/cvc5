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

#include <iostream>

#include "util/exception.h"
#include "parser/language.h"
#include "parser/parser_state.h"
#include "util/command.h"
#include "util/options.h"
#include "expr/expr.h"
#include "smt/smt_engine.h"
#include "util/assert.h"

namespace CVC4 {
namespace parser {

class Parser {

  CVC4::SmtEngine *d_smt;
  std::istream &d_is;
  CVC4::Options *d_opts;
  Language d_lang;
  bool d_interactive;
  void *d_buffer;

public:
  // Constructors
  Parser(CVC4::SmtEngine* smt, Language lang, std::istream& is, CVC4::Options* opts, bool interactive = false) throw();
  // Destructor
  ~Parser() throw();
  // Read the next command.
  CVC4::Command* next() throw();
  // Check if we are done (end of input has been reached)
  bool done() const throw();
  // The same check can be done by using the class Parser's value as
  // a Boolean
  operator bool() const throw() { return done(); }
  void printLocation(std::ostream & out) const throw();
  // Reset any local data that depends on SmtEngine
  void reset() throw();
}; // end of class Parser

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
