/*********************                                           -*- C++ -*-  */
/** theory.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__THEORY__THEORY_H
#define __CVC4__THEORY__THEORY_H

#include "core/cvc4_expr.h"
#include "core/literal.h"

namespace CVC4 {
namespace theory {

/**
 * Base class for T-solvers.  Abstract DPLL(T).
 */
class Theory {
public:
  /**
   * Subclasses of Theory may add additional efforts.  DO NOT CHECK
   * equality with one of these values (e.g. if STANDARD xxx) but
   * rather use range checks (or use the helper functions below).
   * Normally we call QUICK_CHECK or STANDARD; at the leaves we call
   * with MAX_EFFORT.
   */
  enum Effort {
    MIN_EFFORT = 0,
    QUICK_CHECK = 10,
    STANDARD = 50,
    FULL_EFFORT = 100
  };/* enum Effort */

  // TODO add compiler annotation "constant function" here
  static bool minEffortOnly(Effort e)        { return e == MIN_EFFORT; }
  static bool quickCheckOrMore(Effort e)     { return e >= QUICK_CHECK; }
  static bool quickCheckOnly(Effort e)       { return e >= QUICK_CHECK && e < STANDARD; }
  static bool standardEffortOrMore(Effort e) { return e >= STANDARD; }
  static bool standardEffortOnly(Effort e)   { return e >= STANDARD && e < FULL_EFFORT; }
  static bool fullEffort(Effort e)           { return e >= FULL_EFFORT; }

  /**
   * Prepare for an Expr.
   */
  virtual void setup(Expr) = 0;

  /**
   * Assert a literal in the current context.
   */
  virtual void assert(Literal) = 0;

  /**
   * Check the current assignment's consistency.  Return false iff inconsistent.
   */
  virtual bool check(Effort level = FULL_EFFORT) = 0;

  /**
   * T-propagate new literal assignments in the current context.
   */
  // TODO design decision: instead of returning a set of literals
  // here, perhaps we have an interface back into the prop engine
  // where we assert directly.  we might sometimes unknowingly assert
  // something clearly inconsistent (esp. in a parallel context).
  // This would allow the PropEngine to cancel our further work since
  // we're already inconsistent---also could strategize dynamically on
  // whether enough theory prop work has occurred.
  virtual void propagate(Effort level = FULL_EFFORT) = 0;

  /**
   * Return an explanation for the literal (which was previously propagated by this theory)..
   */
  virtual Expr explain(Literal) = 0;

};/* class Theory */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_H */
