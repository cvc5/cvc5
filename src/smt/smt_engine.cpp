/*********************                                                        */
/** smt_engine.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "smt/smt_engine.h"
#include "expr/command.h"
#include "expr/node_builder.h"
#include "util/output.h"
#include "util/exception.h"
#include "util/options.h"
#include "prop/prop_engine.h"

using namespace CVC4::prop;

namespace CVC4 {

SmtEngine::SmtEngine(ExprManager* em, const Options* opts) throw() :
  d_assertions(),
  d_publicEm(em),
  d_nm(em->getNodeManager()),
  d_opts(opts)
{
  d_de = new DecisionEngine();
  d_te = new TheoryEngine(this);
  d_prop = new PropEngine(opts, d_de, d_te);
}

SmtEngine::~SmtEngine() {
   delete d_prop;
   delete d_te;
   delete d_de;
}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nm);
  c->invoke(this);
}

Node SmtEngine::preprocess(const Node& e) {
  return e;
}

void SmtEngine::processAssertionList() {
  for(unsigned i = 0; i < d_assertions.size(); ++i) {
    d_prop->assertFormula(d_assertions[i]);
  }
  d_assertions.clear();
}


Result SmtEngine::check() {
  Debug("smt") << "SMT check()" << std::endl;
  processAssertionList();
  return d_prop->solve();
}

Result SmtEngine::quickCheck() {
  Debug("smt") << "SMT quickCheck()" << std::endl;
  processAssertionList();
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEngine::addFormula(const Node& e) {
  Debug("smt") << "push_back assertion " << e << std::endl;
  d_assertions.push_back(e);
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  Debug("smt") << "SMT checkSat(" << e << ")" << std::endl;
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  Result r = check().asSatisfiabilityResult();
  Debug("smt") << "SMT checkSat(" << e << ") ==> " << r << std::endl;
  return r;
}

Result SmtEngine::query(const BoolExpr& e) {
  Debug("smt") << "SMT query(" << e << ")" << std::endl;
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(d_nm->mkNode(NOT, e.getNode()));
  addFormula(node_e);
  Result r = check().asValidityResult();
  Debug("smt") << "SMT query(" << e << ") ==> " << r << std::endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  Debug("smt") << "SMT assertFormula(" << e << ")" << std::endl;
  NodeManagerScope nms(d_nm);
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& e) {
  Debug("smt") << "SMT simplify(" << e << ")" << std::endl;
  Expr simplify(const Expr& e);
  Unimplemented();
}

void SmtEngine::push() {
}

void SmtEngine::pop() {
}

}/* CVC4 namespace */
