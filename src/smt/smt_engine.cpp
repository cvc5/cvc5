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

SmtEngine::SmtEngine(ExprManager* em, const Options* opts) throw () :
  d_assertions(),
  d_exprManager(em),
  d_nodeManager(em->getNodeManager()),
  d_options(opts)
{
  d_decisionEngine = new DecisionEngine();
  d_theoryEngine = new TheoryEngine(this);
  d_propEngine = new PropEngine(opts, d_decisionEngine, d_theoryEngine);
}

SmtEngine::~SmtEngine() {
  delete d_propEngine;
  delete d_theoryEngine;
  delete d_decisionEngine;
}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nodeManager);
  c->invoke(this);
}

Node SmtEngine::preprocess(const Node& e) {
  return e;
}

void SmtEngine::processAssertionList() {
  for(unsigned i = 0; i < d_assertions.size(); ++i) {
    d_propEngine->assertFormula(d_assertions[i]);
  }
  d_assertions.clear();
}

Result SmtEngine::check() {
  Debug("smt") << "SMT check()" << std::endl;
  processAssertionList();
  return d_propEngine->checkSat();
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
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT checkSat(" << e << ")" << std::endl;
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  Result r = check().asSatisfiabilityResult();
  Debug("smt") << "SMT checkSat(" << e << ") ==> " << r << std::endl;
  return r;
}

Result SmtEngine::query(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT query(" << e << ")" << std::endl;
  Node node_e = preprocess(d_nodeManager->mkNode(NOT, e.getNode()));
  addFormula(node_e);
  Result r = check().asValidityResult();
  Debug("smt") << "SMT query(" << e << ") ==> " << r << std::endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT assertFormula(" << e << ")" << std::endl;
  Node node_e = preprocess(e.getNode());
  addFormula(node_e);
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT simplify(" << e << ")" << std::endl;
  Unimplemented();
}

Model SmtEngine::getModel() {
  NodeManagerScope nms(d_nodeManager);
  Unimplemented();
}

void SmtEngine::push() {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT push()" << std::endl;
  Unimplemented();
}

void SmtEngine::pop() {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT pop()" << std::endl;
  Unimplemented();
}

}/* CVC4 namespace */
