/*********************                                                        */
/*! \file theory_bv_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bit-vector solver interface.
 **
 ** Describes the interface for the internal bit-vector solver of TheoryBV.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__THEORY_BV_SOLVER_H
#define CVC4__THEORY__BV__THEORY_BV_SOLVER_H

#include "theory/bv/theory_bv.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBVSolver
{
 public:
  TheoryBVSolver(TheoryBV& bv)
      : d_bv(bv), d_state(bv.d_state), d_inferManager(*bv.d_inferManager){};

  virtual ~TheoryBVSolver(){};

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

  virtual bool needsCheckLastEffort() = 0;

  virtual void propagate(Theory::Effort e){};

  virtual TrustNode explain(TNode n)
  {
    Unimplemented()
        << "TheoryBVSolver propagated a node but doesn't implement the "
           "Theory::explain() interface!";
    return TrustNode::null();
  };

  virtual bool collectModelInfo(TheoryModel* m) = 0;

  virtual std::string identify() const = 0;

  virtual bool getCurrentSubstitution(int effort,
                                      std::vector<Node>& vars,
                                      std::vector<Node>& subs,
                                      std::map<Node, std::vector<Node>>& exp)
  {
    return false;
  };

  virtual Theory::PPAssertStatus ppAssert(
      TNode in, SubstitutionMap& outSubstitutions) = 0;

  virtual TrustNode ppRewrite(TNode t) { return TrustNode::null(); };

  virtual void ppStaticLearn(TNode in, NodeBuilder<>& learned){};

  virtual void presolve(){};

  virtual void notifySharedTerm(TNode t) = 0;

  virtual EqualityStatus getEqualityStatus(TNode a, TNode b)
  {
    return d_bv.getEqualityStatus(a, b);
  }

  /** Called by abstraction preprocessing pass. */
  virtual bool applyAbstraction(const std::vector<Node>& assertions,
                                std::vector<Node>& new_assertions) = 0;

 protected:
  TheoryBV& d_bv;
  TheoryState& d_state;
  TheoryInferenceManager& d_inferManager;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BV__THEORY_BV_SOLVER_H */
