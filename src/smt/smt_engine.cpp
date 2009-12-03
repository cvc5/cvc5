/*********************                                           -*- C++ -*-  */
/** smt_engine.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "smt/smt_engine.h"
#include "util/exception.h"
#include "util/command.h"

namespace CVC4 {

void SmtEngine::doCommand(Command* c) {
  c->invoke(this);
}

Expr SmtEngine::preprocess(Expr e) {
  return e;
}

void SmtEngine::processAssertionList() {
  for(std::vector<Expr>::iterator i = d_assertions.begin();
      i != d_assertions.end();
      ++i)
    ;//d_expr = d_expr.isNull() ? *i : d_expr.andExpr(*i);
}

Result SmtEngine::check() {
  processAssertionList();
  return Result(Result::VALIDITY_UNKNOWN);
}

Result SmtEngine::quickCheck() {
  processAssertionList();
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEngine::addFormula(Expr e) {
  d_assertions.push_back(e);
}

Result SmtEngine::checkSat(Expr e) {
  e = preprocess(e);
  addFormula(e);
  return check();
}

Result SmtEngine::query(Expr e) {
  e = preprocess(e);
  addFormula(e);
  return check();
}

Result SmtEngine::assert(Expr e) {
  e = preprocess(e);
  addFormula(e);
  return quickCheck();
}

}/* CVC4 namespace */
