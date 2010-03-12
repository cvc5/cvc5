/*********************                                                        */
/** smt_engine.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include "smt/smt_engine.h"
#include "expr/command.h"
#include "expr/node_builder.h"
#include "util/output.h"
#include "util/exception.h"
#include "util/options.h"
#include "prop/prop_engine.h"

using namespace CVC4::prop;
using CVC4::context::Context;

namespace CVC4 {

namespace smt {

/**
 * This is an inelegant solution, but for the present, it will work.
 * The point of this is to separate the public and private portions of
 * the SmtEngine class, so that smt_engine.h doesn't
 * #include "expr/node.h", which is a private CVC4 header (and can lead
 * to linking errors due to the improper inlining of non-visible symbols
 * into user code!).
 *
 * The "real" solution (that which is usually implemented) is to move
 * ALL the implementation to SmtEnginePrivate and maintain a
 * heap-allocated instance of it in SmtEngine.  SmtEngine (the public
 * one) becomes an "interface shell" which simply acts as a forwarder
 * of method calls.
 */
class SmtEnginePrivate {
public:

  /**
   * Pre-process an Node.  This is expected to be highly-variable,
   * with a lot of "source-level configurability" to add multiple
   * passes over the Node.  TODO: may need to specify a LEVEL of
   * preprocessing (certain contexts need more/less ?).
   */
  static Node preprocess(SmtEngine& smt, TNode node);

  /**
   * Adds a formula to the current context.
   */
  static void addFormula(SmtEngine& smt, TNode node);
};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

using ::CVC4::smt::SmtEnginePrivate;

SmtEngine::SmtEngine(ExprManager* em, const Options* opts) throw () :
  d_ctxt(em->getContext()),
  d_exprManager(em),
  d_nodeManager(em->getNodeManager()),
  d_options(opts) {

  NodeManagerScope nms(d_nodeManager);

  d_decisionEngine = new DecisionEngine;
  d_theoryEngine = new TheoryEngine(this, d_ctxt);
  d_propEngine = new PropEngine(opts, d_decisionEngine, d_theoryEngine, d_ctxt);
}

void SmtEngine::shutdown() {
  d_propEngine->shutdown();
  d_theoryEngine->shutdown();
  d_decisionEngine->shutdown();
}

SmtEngine::~SmtEngine() {
  NodeManagerScope nms(d_nodeManager);

  shutdown();

  delete d_propEngine;
  delete d_theoryEngine;
  delete d_decisionEngine;
}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nodeManager);
  c->invoke(this);
}

Node SmtEnginePrivate::preprocess(SmtEngine& smt, TNode e) {
  return smt.d_theoryEngine->preprocess(e);
}

Result SmtEngine::check() {
  Debug("smt") << "SMT check()" << std::endl;
  return d_propEngine->checkSat();
}

Result SmtEngine::quickCheck() {
  Debug("smt") << "SMT quickCheck()" << std::endl;
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEnginePrivate::addFormula(SmtEngine& smt, TNode e) {
  Debug("smt") << "push_back assertion " << e << std::endl;
  smt.d_propEngine->assertFormula(SmtEnginePrivate::preprocess(smt, e));
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT checkSat(" << e << ")" << std::endl;
  SmtEnginePrivate::addFormula(*this, e.getNode());
  Result r = check().asSatisfiabilityResult();
  Debug("smt") << "SMT checkSat(" << e << ") ==> " << r << std::endl;
  return r;
}

Result SmtEngine::query(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT query(" << e << ")" << std::endl;
  SmtEnginePrivate::addFormula(*this, e.getNode().notNode());
  Result r = check().asValidityResult();
  Debug("smt") << "SMT query(" << e << ") ==> " << r << std::endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT assertFormula(" << e << ")" << std::endl;
  SmtEnginePrivate::addFormula(*this, e.getNode());
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
