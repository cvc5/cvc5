/*********************                                                        */
/*! \file smt_engine.h
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
 ** \brief SmtEngine: the main public entry point of libcvc4.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT_ENGINE_H
#define __CVC4__SMT_ENGINE_H

#include <vector>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "context/cdmap_forward.h"
#include "util/result.h"
#include "util/model.h"
#include "util/sexpr.h"
#include "util/hash.h"
#include "smt/modal_exception.h"
#include "smt/no_such_function_exception.h"
#include "smt/bad_option_exception.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

template <bool ref_count> class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;
class NodeHashFunction;
class Command;
class Options;
class TheoryEngine;
class DecisionEngine;

namespace context {
  class Context;
  template <class T> class CDList;
}/* CVC4::context namespace */

namespace prop {
  class PropEngine;
}/* CVC4::prop namespace */

namespace smt {
  /**
   * Representation of a defined function.  We keep these around in
   * SmtEngine to permit expanding definitions late (and lazily), to
   * support getValue() over defined functions, to support user output
   * in terms of defined functions, etc.
   */
  class DefinedFunction;

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

  /** The type of our internal map of defined functions */
  typedef context::CDMap<Node, smt::DefinedFunction, NodeHashFunction>
    DefinedFunctionMap;
  /** The type of our internal assertion list */
  typedef context::CDList<Expr> AssertionList;

  /** Our Context */
  context::Context* d_context;
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
  /** An index of our defined functions */
  DefinedFunctionMap* d_definedFunctions;
  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in interactive mode.
   */
  AssertionList* d_assertionList;

  /**
   * Whether or not we have added any
   * assertions/declarations/definitions since the last checkSat/query
   * (and therefore we're not responsible for an assignment).
   */
  bool d_haveAdditions;

  /**
   * Result of last checkSat/query.
   */
  Result d_lastResult;

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

  /**
   * Fully type-check the argument, and also type-check that it's
   * actually Boolean.
   */
  void ensureBoolean(const BoolExpr& e);

  friend class ::CVC4::smt::SmtEnginePrivate;

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
   * Set information about the script executing.
   */
  void setInfo(const std::string& key, const SExpr& value)
    throw(BadOptionException);

  /**
   * Query information about the SMT environment.
   */
  const SExpr& getInfo(const std::string& key) const
    throw(BadOptionException);

  /**
   * Set an aspect of the current SMT execution environment.
   */
  void setOption(const std::string& key, const SExpr& value)
    throw(BadOptionException);

  /**
   * Get an aspect of the current SMT execution environment.
   */
  const SExpr& getOption(const std::string& key) const
    throw(BadOptionException);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  void defineFunction(Expr func,
                      const std::vector<Expr>& formals,
                      Expr formula);

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
   * Get the assigned value of an expr (only if immediately preceded
   * by a SAT or INVALID query).  Only permitted if the SmtEngine is
   * set to operate interactively and produce-models is on.
   */
  Expr getValue(Expr e) throw(ModalException, AssertionException);

  /**
   * Get the assignment (only if immediately preceded by a SAT or
   * INVALID query).  Only permitted if the SmtEngine is set to
   * operate interactively and produce-assignments is on.
   */
  SExpr getAssignment() throw(ModalException, AssertionException);

  /**
   * Get the current set of assertions.  Only permitted if the
   * SmtEngine is set to operate interactively.
   */
  std::vector<Expr> getAssertions() throw(ModalException, AssertionException);

  /**
   * Push a user-level context.
   */
  void push();

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   */
  void pop();

};/* class SmtEngine */

}/* CVC4 namespace */

#endif /* __CVC4__SMT_ENGINE_H */
