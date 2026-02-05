/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-vector solver interface.
 *
 * Describes the interface for the internal bit-vector solver of TheoryBV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SOLVER_H
#define CVC5__THEORY__BV__BV_SOLVER_H

#include "smt/env_obj.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

class BVSolver : protected EnvObj
{
 public:
  BVSolver(Env& env, TheoryState& state, TheoryInferenceManager& inferMgr)
      : EnvObj(env), d_state(state), d_im(inferMgr){};

  virtual ~BVSolver() {}

  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  virtual bool needsEqualityEngine(CVC5_UNUSED EeSetupInfo& esi)
  {
    return false;
  }

  virtual void finishInit(){};

  virtual void preRegisterTerm(TNode n) = 0;

  /**
   * Forwarded from TheoryBV::preCheck().
   */
  virtual bool preCheck(
      CVC5_UNUSED Theory::Effort level = Theory::Effort::EFFORT_FULL)
  {
    return false;
  }
  /**
   * Forwarded from TheoryBV::postCheck().
   */
  virtual void postCheck(
      CVC5_UNUSED Theory::Effort level = Theory::Effort::EFFORT_FULL) {};
  /**
   * Forwarded from TheoryBV:preNotifyFact().
   */
  virtual bool preNotifyFact(CVC5_UNUSED TNode atom,
                             CVC5_UNUSED bool pol,
                             CVC5_UNUSED TNode fact,
                             CVC5_UNUSED bool isPrereg,
                             CVC5_UNUSED bool isInternal)
  {
    return false;
  }
  /**
   * Forwarded from TheoryBV::notifyFact().
   */
  virtual void notifyFact(CVC5_UNUSED TNode atom,
                          CVC5_UNUSED bool pol,
                          CVC5_UNUSED TNode fact,
                          CVC5_UNUSED bool isInternal)
  {
  }

  virtual bool needsCheckLastEffort() { return false; }

  virtual void propagate(CVC5_UNUSED Theory::Effort e) {}

  virtual TrustNode explain(CVC5_UNUSED TNode n)
  {
    Unimplemented() << "BVSolver propagated a node but doesn't implement the "
                       "BVSolver::explain() interface!";
    return TrustNode::null();
  }

  /** Additionally collect terms relevant for collecting model values. */
  virtual void computeRelevantTerms(CVC5_UNUSED std::set<Node>& termSet) {}

  /** Collect model values in m based on the relevant terms given by termSet */
  virtual bool collectModelValues(TheoryModel* m,
                                  const std::set<Node>& termSet) = 0;

  virtual std::string identify() const = 0;

  virtual TrustNode ppRewrite(CVC5_UNUSED TNode t) { return TrustNode::null(); }

  virtual void ppStaticLearn(CVC5_UNUSED TNode in,
                             CVC5_UNUSED std::vector<TrustNode>& learned)
  {
  }

  virtual void presolve() {}

  virtual void notifySharedTerm(CVC5_UNUSED TNode t) {}

  virtual EqualityStatus getEqualityStatus(CVC5_UNUSED TNode a,
                                           CVC5_UNUSED TNode b)
  {
    return EqualityStatus::EQUALITY_UNKNOWN;
  }

  /**
   * Get the current value of `node`.
   *
   * The `initialize` flag indicates whether bits should be zero-initialized
   * if they don't have a value yet.
   */
  virtual Node getValue(CVC5_UNUSED TNode node, CVC5_UNUSED bool initialize)
  {
    return Node::null();
  }

 protected:
  TheoryState& d_state;
  TheoryInferenceManager& d_im;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__BV_SOLVER_H */
