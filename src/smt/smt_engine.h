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
#include "smt/noninteractive_exception.h"
#include "smt/bad_option.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

namespace context {
  class Context;
  template <class T> class CDList;
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
private:

  /** A name/type pair, used for signatures */
  typedef std::pair<std::string, Type> TypedArg;
  /** A vector of typed formals, and a return type */
  typedef std::pair<std::vector<TypedArg>, Type> FunctionSignature;
  /** The type of our internal map of defined functions */
  typedef context::CDMap<std::string, std::pair<FunctionSignature, Expr>,
    StringHashFunction>
    FunctionMap;

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
  FunctionMap* d_functions;
  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in interactive mode.
   */
  AssertionList* d_assertionList;

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
   * Set information about the script executing.
   */
  void setInfo(const std::string& key, const SExpr& value) throw(BadOption);

  /**
   * Query information about the SMT environment.
   */
  const SExpr& getInfo(const std::string& key) const throw(BadOption);

  /**
   * Set an aspect of the current SMT execution environment.
   */
  void setOption(const std::string& key, const SExpr& value) throw(BadOption);

  /**
   * Get an aspect of the current SMT execution environment.
   */
  const SExpr& getOption(const std::string& key) const throw(BadOption);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  void defineFunction(const std::string& name,
                      const std::vector<std::pair<std::string, Type> >& args,
                      Type type,
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
   * Get a (counter)model (only if preceded by a SAT or INVALID query).
   */
  Model getModel();

  /**
   * Get the assigned value of a term (only if preceded by a SAT or
   * INVALID query).
   */
  Expr getValue(Expr term);

  /**
   * Get the current set of assertions.
   */
  std::vector<Expr> getAssertions() throw(NoninteractiveException);

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
