/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_BAGS_H
#define CVC5__THEORY__BAGS__THEORY_BAGS_H

#include "theory/bags/bag_solver.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/bags/bags_statistics.h"
#include "theory/bags/inference_generator.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"

namespace cvc5 {
namespace theory {
namespace bags {

class TheoryBags : public Theory
{
 public:
  /** Constructs a new instance of TheoryBags w.r.t. the provided contexts. */
  TheoryBags(Env& env, OutputChannel& out, Valuation valuation);
  ~TheoryBags() override;

  //--------------------------------- initialization
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
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization

  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort effort) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  TrustNode explain(TNode) override;
  Node getModelValue(TNode) override;
  std::string identify() const override { return "THEORY_BAGS"; }
  void preRegisterTerm(TNode n) override;
  void presolve() override;

 private:
  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public TheoryEqNotifyClass
  {
   public:
    NotifyClass(TheoryBags& theory, TheoryInferenceManager& inferenceManager)

        : TheoryEqNotifyClass(inferenceManager), d_theory(theory)
    {
    }
    void eqNotifyNewClass(TNode n) override;
    void eqNotifyMerge(TNode n1, TNode n2) override;
    void eqNotifyDisequal(TNode n1, TNode n2, TNode reason) override;

   private:
    TheoryBags& d_theory;
  };

  /** The state of the bags solver at full effort */
  SolverState d_state;
  /** The inference manager */
  InferenceManager d_im;
  /** The inference generator */
  InferenceGenerator d_ig;
  /** Instance of the above class */
  NotifyClass d_notify;
  /** Statistics for the theory of bags. */
  BagsStatistics d_statistics;
  /** The theory rewriter for this theory. */
  BagsRewriter d_rewriter;
  /** The term registry for this theory */
  TermRegistry d_termReg;
  /** the main solver for bags */
  BagSolver d_solver;

  void eqNotifyNewClass(TNode n);
  void eqNotifyMerge(TNode n1, TNode n2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
}; /* class TheoryBags */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAGS__THEORY_BAGS_H */
