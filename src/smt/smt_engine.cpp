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

SmtEngine::SmtEngine(ExprManager* em, Options* opts) throw() :
    d_public_em(em),
    d_em(em->getNodeManager()),
    d_opts(opts),
    d_de(),
    d_te(),
    d_prop(d_de, d_te) {
  }

SmtEngine::~SmtEngine() {

}

void SmtEngine::doCommand(Command* c) {
  c->invoke(this);
}

Node SmtEngine::preprocess(const Node& e) {
  return e;
}

Node SmtEngine::processAssertionList() {
  Node asserts;
  for(std::vector<Node>::iterator i = d_assertions.begin();
      i != d_assertions.end();
      ++i) {
    asserts = asserts.isNull() ? *i : d_em->mkNode(AND, asserts, *i);
  }
  return asserts;
}

Result SmtEngine::check() {
  Node asserts = processAssertionList();
  d_prop.solve(asserts);
  return Result(Result::VALIDITY_UNKNOWN);
}

Result SmtEngine::quickCheck() {
  processAssertionList();
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEngine::addFormula(const Node& e) {
  d_assertions.push_back(e);
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return check();
}

Result SmtEngine::query(const BoolExpr& e) {
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return check();
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return quickCheck();
}

}/* CVC4 namespace */
