/*********************                                                        */
/*! \file theory_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A theory state for Theory
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_STATE_H
#define CVC4__THEORY__THEORY_STATE_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {

namespace eq {
class EqualityEngine;
}

class TheoryState
{
 public:
  TheoryState(context::Context* c, context::UserContext* u, Valuation val);
  virtual ~TheoryState() {}
  /**
   * Set equality engine, where ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  /** Get the SAT context */
  context::Context* getSatContext() const;
  /** Get the user context */
  context::UserContext* getUserContext() const;
  //-------------------------------------- equality information
  /** Is t registered as a term in the equality engine of this class? */
  virtual bool hasTerm(TNode a) const;
  /**
   * Get the representative of t in the equality engine of this class, or t
   * itself if it is not registered as a term.
   */
  virtual TNode getRepresentative(TNode t) const;
  /**
   * Are a and b equal according to the equality engine of this class? Also
   * returns true if a and b are identical.
   */
  virtual bool areEqual(TNode a, TNode b) const;
  /**
   * Are a and b disequal according to the equality engine of this class? Also
   * returns true if the representative of a and b are distinct constants.
   */
  virtual bool areDisequal(TNode a, TNode b) const;
  /** get equality engine */
  eq::EqualityEngine* getEqualityEngine() const;
  //-------------------------------------- end equality information
  /**
   * Set that the current state of the solver is in conflict. This should be
   * called immediately after a call to conflict(...) on the output channel of
   * the theory.
   */
  virtual void notifyInConflict();
  /** Are we currently in conflict? */
  virtual bool isInConflict() const;

  /** Returns true if lit is a SAT literal. */
  virtual bool isSatLiteral(TNode lit) const;
  /**
   * Returns pointer to model. This model is only valid during last call effort
   * check.
   */
  TheoryModel* getModel();

 protected:
  /** Pointer to the SAT context object used by the theory. */
  context::Context* d_context;
  /** Pointer to the user context object used by the theory. */
  context::UserContext* d_ucontext;
  /**
   * The valuation proxy for the Theory to communicate back with the
   * theory engine (and other theories).
   */
  Valuation d_valuation;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
  /** Are we in conflict? */
  context::CDO<bool> d_conflict;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SOLVER_STATE_H */
