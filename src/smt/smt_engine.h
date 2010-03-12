/*********************                                                        */
/** smt_engine.h
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
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#ifndef __CVC4__SMT_ENGINE_H
#define __CVC4__SMT_ENGINE_H

#include <vector>

#include "cvc4_config.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/result.h"
#include "util/model.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

namespace context {
  class Context;
}/* CVC4::context namespace */

class Command;
class Options;
class TheoryEngine;
class DecisionEngine;

namespace prop {
  class PropEngine;
}/* CVC4::prop namespace */

namespace smt {
  class SmtEnginePrivate;
}/* CVC4::smt namespace */

// TODO: SAT layer (esp. CNF- versus non-clausal solvers under the
// hood): use a type parameter and have check() delegate, or subclass
// SmtEngine and override check()?
//
// Probably better than that is to have a configuration object that
// indicates which passes are desired.  The configuration occurs
// elsewhere (and can even occur at runtime).  A simple "pass manager"
// of sorts determines check()'s behavior.
//
// The CNF conversion can go on in PropEngine.

class CVC4_PUBLIC SmtEngine {

public:

  /**
   * Construct an SmtEngine with the given expression manager and user options.
   */
  SmtEngine(ExprManager* em, const Options* opts) throw();

  /**
   * Destruct the SMT engine.
   */
  ~SmtEngine();

  /**
   * Execute a command.
   */
  void doCommand(Command*);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  Result assertFormula(const BoolExpr& e);

  /**
   * Add a formula to the current context and call check().  Returns
   * true iff consistent.
   */
  Result query(const BoolExpr& e);

  /**
   * Add a formula to the current context and call check().  Returns
   * true iff consistent.
   */
  Result checkSat(const BoolExpr& e);

  /**
   * Simplify a formula without doing "much" work.  Requires assist
   * from the SAT Engine.
   */
  Expr simplify(const Expr& e);

  /**
   * Get a (counter)model (only if preceded by a SAT or INVALID query).
   */
  Model getModel();

  /**
   * Push a user-level context.
   */
  void push();

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   */
  void pop();

private:

  /** Our Context */
  CVC4::context::Context* d_ctxt;

  /** Our expression manager */
  ExprManager* d_exprManager;

  /** Out internal expression/node manager */
  NodeManager* d_nodeManager;

  /** User-level options */
  const Options* d_options;

  /** The decision engine */
  DecisionEngine* d_decisionEngine;

  /** The decision engine */
  TheoryEngine* d_theoryEngine;

  /** The propositional engine */
  prop::PropEngine* d_propEngine;

  // preprocess() and addFormula() used to be housed here; they are
  // now in an SmtEnginePrivate class.  See the comment in
  // smt_engine.cpp.

  /**
   * This is called by the destructor, just before destroying the
   * PropEngine, TheoryEngine, and DecisionEngine (in that order).  It
   * is important because there are destruction ordering issues
   * between PropEngine and Theory.
   */
  void shutdown();

  /**
   * Full check of consistency in current context.  Returns true iff
   * consistent.
   */
  Result check();

  /**
   * Quick check of consistency in current context: calls
   * processAssertionList() then look for inconsistency (based only on
   * that).
   */
  Result quickCheck();

  friend class ::CVC4::smt::SmtEnginePrivate;

};/* class SmtEngine */

}/* CVC4 namespace */

#endif /* __CVC4__SMT_ENGINE_H */
