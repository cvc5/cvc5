/*********************                                                        */
/*! \file bv_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bit-vector solver interface.
 **
 ** Describes the interface for the internal bit-vector solver of TheoryBV.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BV_SOLVER_H
#define CVC4__THEORY__BV__BV_SOLVER_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BVSolver
{
 public:
  BVSolver(TheoryState& state, TheoryInferenceManager& inferMgr)
      : d_state(state), d_inferManager(inferMgr){};

  virtual ~BVSolver(){};

  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  virtual bool needsEqualityEngine(EeSetupInfo& esi) { return false; }

  virtual void finishInit(){};

  virtual void preRegisterTerm(TNode n) = 0;

  /**
   * Forwarded from TheoryBV::preCheck().
   */
  virtual bool preCheck(Theory::Effort level = Theory::Effort::EFFORT_FULL)
  {
    return false;
  }
  /**
   * Forwarded from TheoryBV::postCheck().
   */
  virtual void postCheck(Theory::Effort level = Theory::Effort::EFFORT_FULL){};
  /**
   * Forwarded from TheoryBV:preNotifyFact().
   */
  virtual bool preNotifyFact(
      TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
  {
    return false;
  }
  /**
   * Forwarded from TheoryBV::notifyFact().
   */
  virtual void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) {}

  virtual bool needsCheckLastEffort() { return false; }

  virtual void propagate(Theory::Effort e){};

  virtual TrustNode explain(TNode n)
  {
    Unimplemented() << "BVSolver propagated a node but doesn't implement the "
                       "BVSolver::explain() interface!";
    return TrustNode::null();
  }

  /** Collect model values in m based on the relevant terms given by termSet */
  virtual bool collectModelValues(TheoryModel* m,
                                  const std::set<Node>& termSet) = 0;

  virtual std::string identify() const = 0;

  virtual Theory::PPAssertStatus ppAssert(
      TNode in, SubstitutionMap& outSubstitutions) = 0;

  virtual TrustNode ppRewrite(TNode t) { return TrustNode::null(); };

  virtual void ppStaticLearn(TNode in, NodeBuilder<>& learned){};

  virtual void presolve(){};

  virtual void notifySharedTerm(TNode t) {}

  virtual EqualityStatus getEqualityStatus(TNode a, TNode b)
  {
    return EqualityStatus::EQUALITY_UNKNOWN;
  }

  /** Called by abstraction preprocessing pass. */
  virtual bool applyAbstraction(const std::vector<Node>& assertions,
                                std::vector<Node>& new_assertions)
  {
    new_assertions.insert(
        new_assertions.end(), assertions.begin(), assertions.end());
    return false;
  };

 protected:
  TheoryState& d_state;
  TheoryInferenceManager& d_inferManager;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BV__BV_SOLVER_H */
