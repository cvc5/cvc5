/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of bit-vectors.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__THEORY_BV_H
#define CVC5__THEORY__BV__THEORY_BV_H

#include "theory/bv/theory_bv_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/theory_state.h"

namespace cvc5::internal {

class ProofRuleChecker;

namespace theory {
namespace bv {

class BVSolver;

class TheoryBV : public Theory
{
 public:
  TheoryBV(Env& env,
           OutputChannel& out,
           Valuation valuation,
           std::string name = "");

  ~TheoryBV();

  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;

  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  void finishInit() override;

  void preRegisterTerm(TNode n) override;

  bool preCheck(Effort e) override;

  void postCheck(Effort e) override;

  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;

  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;

  bool needsCheckLastEffort() override;

  void propagate(Effort e) override;

  TrustNode explain(TNode n) override;

  void computeRelevantTerms(std::set<Node>& termSet) override;

  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  std::string identify() const override { return std::string("TheoryBV"); }

  PPAssertStatus ppAssert(TrustNode in,
                          TrustSubstitutionMap& outSubstitutions) override;

  TrustNode ppRewrite(TNode t, std::vector<SkolemLemma>& lems) override;

  void ppStaticLearn(TNode in, NodeBuilder& learned) override;

  void presolve() override;

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

 private:
  void notifySharedTerm(TNode t) override;

  Node getValue(TNode node);

  /** Internal BV solver. */
  std::unique_ptr<BVSolver> d_internal;

  /** The theory rewriter for this theory. */
  TheoryBVRewriter d_rewriter;

  /** A (default) theory state object */
  TheoryState d_state;

  /** A (default) theory inference manager. */
  TheoryInferenceManager d_im;

  /** The notify class for equality engine. */
  TheoryEqNotifyClass d_notify;

  /** Flag indicating whether `d_modelCache` should be invalidated. */
  context::CDO<bool> d_invalidateModelCache;

  /**
   * Cache for getValue() calls.
   *
   * Is cleared at the beginning of a getValue() call if the
   * `d_invalidateModelCache` flag is set to true.
   */
  std::unordered_map<Node, Node> d_modelCache;

  /** TheoryBV statistics. */
  struct Statistics
  {
    Statistics(StatisticsRegistry& reg, const std::string& name);
    IntStat d_solveSubstitutions;
  } d_stats;

}; /* class TheoryBV */

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__THEORY_BV_H */
