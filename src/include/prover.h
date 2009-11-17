/*********************                                           -*- C++ -*-  */
/** prover.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4_PROVER_H
#define __CVC4_PROVER_H

#include <vector>
#include "expr.h"
#include "result.h"
#include "model.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

// TODO: SAT layer (esp. CNF- versus non-clausal solvers under the
// hood): use a type parameter and have check() delegate, or subclass
// Prover and override check()?
//
// Probably better than that is to have a configuration object that
// indicates which passes are desired.  The configuration occurs
// elsewhere (and can even occur at runtime).  A simple "pass manager"
// of sorts determines check()'s behavior.
//
// The CNF conversion can go on in PropEngine.

class Prover {
  /** Current set of assertions. */
  // TODO: make context-aware to handle user-level push/pop.
  std::vector<Expr> d_assertList;

private:
  /**
   * Pre-process an Expr.  This is expected to be highly-variable,
   * with a lot of "source-level configurability" to add multiple
   * passes over the Expr.  TODO: may need to specify a LEVEL of
   * preprocessing (certain contexts need more/less ?).
   */
  void preprocess(Expr);

  /**
   * Adds a formula to the current context.
   */
  void addFormula(Expr);

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
   * Process the assertion list: for literals and conjunctions of
   * literals, assert to T-solver.
   */
  void processAssertionList();

public:
  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  Result assert(Expr);

  /**
   * Add a formula to the current context and call check().  Returns
   * true iff consistent.
   */
  Result query(Expr);

  /**
   * Simplify a formula without doing "much" work.  Requires assist
   * from the SAT Engine.
   */
  Expr simplify(Expr);

  /**
   * Get a (counter)model (only if preceded by a SAT or INVALID query.
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
};/* class Prover */

} /* CVC4 namespace */

#endif /* __CVC4_PROVER_H */
