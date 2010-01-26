/*********************                                           -*- C++ -*-  */
/** smt_engine.cpp
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
 **/

#include "smt/smt_engine.h"
#include "util/exception.h"
#include "util/command.h"
#include "util/output.h"
#include "expr/node_builder.h"

namespace CVC4 {

SmtEngine::SmtEngine(ExprManager* em, Options* opts) throw() :
  d_assertions(),
  d_public_em(em),
  d_nm(em->getNodeManager()),
  d_opts(opts),
  d_de(),
  d_te(),
  d_prop(d_de, d_te) {
}

SmtEngine::~SmtEngine() {

}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nm);
  c->invoke(this);
}

Node SmtEngine::preprocess(const Node& e) {
  if(e.getKind() == NOT) {
    if(e[0].getKind() == TRUE) {
      return d_nm->mkNode(FALSE);
    } else if(e[0].getKind() == FALSE) {
      return d_nm->mkNode(TRUE);
    } else if(e[0].getKind() == NOT) {
      return preprocess(e[0][0]);
    }
  }
  return e;
}

Node SmtEngine::processAssertionList() {
  if(d_assertions.size() == 1) {
    return d_assertions[0];
  }

  NodeBuilder<> asserts(AND);
  for(std::vector<Node>::iterator i = d_assertions.begin();
      i != d_assertions.end();
      ++i) {
    asserts << *i;
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
  Debug("smt") << "push_back assertion " << e << std::endl;
  d_assertions.push_back(e);
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return check();
}

Result SmtEngine::query(const BoolExpr& e) {
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(d_nm->mkNode(NOT, e.getNode()));
  addFormula(node_e);
  return check();
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return quickCheck();
}

Expr SmtEngine::simplify(const Expr& e) {
  Expr simplify(const Expr& e);
  Unimplemented();
}

}/* CVC4 namespace */
