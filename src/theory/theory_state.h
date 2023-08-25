/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A theory state for Theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_STATE_H
#define CVC5__THEORY__THEORY_STATE_H

#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env.h"
#include "smt/env_obj.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {

namespace eq {
class EqualityEngine;
}

class TheoryState : protected EnvObj
{
 public:
  TheoryState(Env& env,
              Valuation val);
  virtual ~TheoryState() {}
  /**
   * Set equality engine, where ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  //-------------------------------------- equality information
  /** Is t registered as a term in the equality engine of this class? */
  virtual bool hasTerm(TNode t) const;
  /** Add term t to the equality engine if it is not registered */
  virtual void addTerm(TNode t);
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
  /** get list of members in the equivalence class of a */
  virtual void getEquivalenceClass(Node a, std::vector<Node>& eqc) const;
  /**
   * Add pred as a trigger predicate to the equality engine of the theory
   * that owns this state. If the option prereg-check-sat-assert is true,
   * this first checks whether pred has already been asserted. If so, then
   * the trigger is not added. In this care, pred is added as a non-trigger
   * term to the equality engine instead.
   */
  void addEqualityEngineTriggerPredicate(TNode pred);
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
  /**
   * Returns a pointer to the sort inference module, which lives in TheoryEngine
   * and is non-null when options::sortInference is true.
   */
  SortInference* getSortInference();

  /** Returns true if n has a current SAT assignment and stores it in value. */
  virtual bool hasSatValue(TNode n, bool& value) const;

  //------------------------------------------- access methods for assertions
  /**
   * The following methods are intended only to be used in limited use cases,
   * for cases where a theory (e.g. quantifiers) requires knowing about the
   * assertions from other theories.
   */
  /** The beginning iterator of facts for theory tid.*/
  context::CDList<Assertion>::const_iterator factsBegin(TheoryId tid);
  /** The beginning iterator of facts for theory tid.*/
  context::CDList<Assertion>::const_iterator factsEnd(TheoryId tid);

  /** Get the underlying valuation class */
  Valuation& getValuation();

 protected:
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
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SOLVER_STATE_H */
