/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"
#include "theory/ee_setup_info.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;

namespace linear {
class ArithCongruenceManager;
}

/**
 * The arithmetic equality solver. This class manages arithmetic equalities
 * in the default way via an equality engine, or defers to the congruence
 * manager of linear arithmetic if setCongruenceManager is called on a
 * non-null congruence manager.
 *
 * Since arithmetic has multiple ways of propagating literals, it tracks
 * the literals that it propagates and only explains the literals that
 * originated from this class.
 */
class EqualitySolver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  EqualitySolver(Env& env, TheoryState& astate, InferenceManager& aim);
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

  /** Set the congruence manager, which will be notified of propagations */
  void setCongruenceManager(linear::ArithCongruenceManager* acm);

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
  TheoryState& d_astate;
  /** reference to parent */
  InferenceManager& d_aim;
  /** Equality solver notify */
  EqualitySolverNotify d_notify;
  /** Pointer to the equality engine */
  eq::EqualityEngine* d_ee;
  /** The literals we have propagated */
  NodeSet d_propLits;
  /** Pointer to the congruence manager, for notifications of propagations */
  linear::ArithCongruenceManager* d_acm;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
