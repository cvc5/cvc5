/*********************                                           -*- C++ -*-  */
/** parser.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser implementation.
 **/

#include <iostream>

#include "cvc4_config.h"
#include "parser/parser.h"
#include "util/command.h"
#include "util/assert.h"
#include "parser/parser_state.h"
#include "parser/parser_exception.h"

int CVC4_PUBLIC smtlibparse();
int CVC4_PUBLIC PLparse();
extern "C" int smtlibdebug, PLdebug;

using namespace std;
using namespace CVC4;

namespace CVC4 {
namespace parser {

ParserState CVC4_PUBLIC *_global_parser_state = 0;

bool Parser::done() const {
  return _global_parser_state->done();
}

Command* Parser::parseNextCommand(bool verbose) {
  switch(d_lang) {
  case PL:
    PLdebug = verbose;
    PLparse();
    cout << "getting command" << endl;
    return _global_parser_state->getCommand();
  case SMTLIB:
    smtlibdebug = verbose;
    smtlibparse();
    return _global_parser_state->getCommand();
  default:
    Unhandled();
  }
  return new EmptyCommand;
}

Parser::~Parser() {
  //delete d_data;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

