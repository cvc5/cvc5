/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface.
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include "smt/smt_engine.h"
#include "smt/noninteractive_exception.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "expr/command.h"
#include "expr/node_builder.h"
#include "util/output.h"
#include "util/exception.h"
#include "util/options.h"
#include "prop/prop_engine.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::prop;
using namespace CVC4::context;

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
  static Node preprocess(SmtEngine& smt, TNode n);

  /**
   * Adds a formula to the current context.
   */
  static void addFormula(SmtEngine& smt, TNode n);
};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

using ::CVC4::smt::SmtEnginePrivate;

SmtEngine::SmtEngine(ExprManager* em, const Options* opts) throw () :
  d_context(em->getContext()),
  d_exprManager(em),
  d_nodeManager(em->getNodeManager()),
  d_options(opts),
  /* These next few are initialized below, after we have a NodeManager
   * in scope. */
  d_decisionEngine(NULL),
  d_theoryEngine(NULL),
  d_propEngine(NULL),
  d_assertionList(NULL) {

  NodeManagerScope nms(d_nodeManager);

  d_decisionEngine = new DecisionEngine;
  // We have mutual dependancy here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context, opts);
  d_propEngine = new PropEngine(opts, d_decisionEngine,
                                d_theoryEngine, d_context);
  d_theoryEngine->setPropEngine(d_propEngine);

  if(d_options->interactive) {
    d_assertionList = new(true) CDList<Expr>(d_context);
  }
}

void SmtEngine::shutdown() {
  d_propEngine->shutdown();
  d_theoryEngine->shutdown();
  d_decisionEngine->shutdown();
}

SmtEngine::~SmtEngine() {
  NodeManagerScope nms(d_nodeManager);

  shutdown();

  ::delete d_assertionList;

  delete d_theoryEngine;
  delete d_propEngine;
  delete d_decisionEngine;
}

void SmtEngine::doCommand(Command* c) {
  NodeManagerScope nms(d_nodeManager);
  c->invoke(this);
}

void SmtEngine::setInfo(const std::string& key, const SExpr& value) throw(BadOption) {
  // FIXME implement me
}

const SExpr& SmtEngine::getInfo(const std::string& key) const throw(BadOption) {
  // FIXME implement me
  throw BadOption();
}

void SmtEngine::setOption(const std::string& key, const SExpr& value) throw(BadOption) {
  // FIXME implement me
}

const SExpr& SmtEngine::getOption(const std::string& key) const throw(BadOption) {
  // FIXME implement me
  throw BadOption();
}

void SmtEngine::defineFunction(const string& name,
                               const vector<pair<string, Type> >& args,
                               Type type,
                               Expr formula) {
  NodeManagerScope nms(d_nodeManager);
  Unimplemented();
}

Node SmtEnginePrivate::preprocess(SmtEngine& smt, TNode n) {
  return smt.d_theoryEngine->preprocess(n);
}

Result SmtEngine::check() {
  Debug("smt") << "SMT check()" << endl;
  return d_propEngine->checkSat();
}

Result SmtEngine::quickCheck() {
  Debug("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN);
}

void SmtEnginePrivate::addFormula(SmtEngine& smt, TNode n) {
  Debug("smt") << "push_back assertion " << n << endl;
  smt.d_propEngine->assertFormula(SmtEnginePrivate::preprocess(smt, n));
}

Result SmtEngine::checkSat(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT checkSat(" << e << ")" << endl;
  SmtEnginePrivate::addFormula(*this, e.getNode());
  Result r = check().asSatisfiabilityResult();
  Debug("smt") << "SMT checkSat(" << e << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::query(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT query(" << e << ")" << endl;
  SmtEnginePrivate::addFormula(*this, e.getNode().notNode());
  Result r = check().asValidityResult();
  Debug("smt") << "SMT query(" << e << ") ==> " << r << endl;
  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT assertFormula(" << e << ")" << endl;
  SmtEnginePrivate::addFormula(*this, e.getNode());
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& e) {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT simplify(" << e << ")" << endl;
  Unimplemented();
}

Model SmtEngine::getModel() {
  NodeManagerScope nms(d_nodeManager);
  Unimplemented();
}

Expr SmtEngine::getValue(Expr term) {
  NodeManagerScope nms(d_nodeManager);
  Unimplemented();
}

vector<Expr> SmtEngine::getAssertions() throw(NoninteractiveException) {
  if(!d_options->interactive) {
    const char* msg =
      "Cannot query the current assertion list when not in interactive mode.";
    throw NoninteractiveException(msg);
  }
  Assert(d_assertionList != NULL);
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
}

void SmtEngine::push() {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT push()" << endl;
  Unimplemented();
}

void SmtEngine::pop() {
  NodeManagerScope nms(d_nodeManager);
  Debug("smt") << "SMT pop()" << endl;
  Unimplemented();
}

}/* CVC4 namespace */
