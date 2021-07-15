/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic equality solver
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__EQUALITY_SOLVER_H
#define CVC5__THEORY__ARITH__EQUALITY_SOLVER_H

#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/trust_node.h"
#include "theory/arith/arith_state.h"
#include "theory/ee_setup_info.h"
#include "theory/uf/equality_engine.h"

namespace cvc5 {
namespace theory {
namespace arith {

class InferenceManager;

/**
 * The arithmetic equality solver. This class manages arithmetic equalities
 * in the default way via an equality engine.
 *
 * Since arithmetic has multiple ways of propagating literals, it tracks
 * the literals that it propagates and only explains the literals that
 * originated from this class.
 */
class EqualitySolver
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  EqualitySolver(ArithState& astate, InferenceManager& aim);
  ~EqualitySolver() {}
  //--------------------------------- initialization
  /**
   * Returns true if we need an equality engine, see
   * Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi);
  /**
   * Finish initialize
   */
  void finishInit();
  //--------------------------------- end initialization
  /**
   * Pre-notify fact, return true if we are finished processing, false if
   * we wish to assert the fact to the equality engine of this class.
   */
  bool preNotifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal);
  /**
   * Return an explanation for the literal lit (which was previously propagated
   * by this solver).
   */
  TrustNode explain(TNode lit);

 private:
  /** Notification class from the equality engine */
  class EqualitySolverNotify : public eq::EqualityEngineNotify
  {
   public:
    EqualitySolverNotify(EqualitySolver& es) : d_es(es) {}

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;

    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override {}
    void eqNotifyMerge(TNode t1, TNode t2) override {}
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}

   private:
    /** reference to parent */
    EqualitySolver& d_es;
  };
  /** Propagate literal */
  bool propagateLit(Node lit);
  /** Conflict when two constants merge */
  void conflictEqConstantMerge(TNode a, TNode b);
  /** reference to the state */
  ArithState& d_astate;
  /** reference to parent */
  InferenceManager& d_aim;
  /** Equality solver notify */
  EqualitySolverNotify d_notify;
  /** Pointer to the equality engine */
  eq::EqualityEngine* d_ee;
  /** The literals we have propagated */
  NodeSet d_propLits;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
