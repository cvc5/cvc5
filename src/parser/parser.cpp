/*********************                                           -*- C++ -*-  */
/** parser.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
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
#include <fstream>

#include "parser.h"
#include "util/command.h"
#include "util/Assert.h"
#include "parser_exception.h"
#include "parser/antlr_parser.h"
#include "parser/smt/generated/AntlrSmtParser.hpp"
#include "parser/smt/generated/AntlrSmtLexer.hpp"
#include "parser/cvc/generated/AntlrCvcParser.hpp"
#include "parser/cvc/generated/AntlrCvcLexer.hpp"

using namespace std;

namespace CVC4 {
namespace parser {

Parser::Parser(ExprManager* em) :
  d_expr_manager(em), d_done(false) {
}

void Parser::setDone(bool done) {
  d_done = done;
}

bool Parser::done() const {
  return d_done;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */
