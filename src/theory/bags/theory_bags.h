/*********************                                                        */
/*! \file theory_bags.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_BAGS_H
#define CVC4__THEORY__BAGS__THEORY_BAGS_H

#include <memory>

#include "theory/bags/bags_rewriter.h"
#include "theory/bags/bags_statistics.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

class TheoryBags : public Theory
{
 public:
  /** Constructs a new instance of TheoryBags w.r.t. the provided contexts. */
  TheoryBags(context::Context* c,
             context::UserContext* u,
             OutputChannel& out,
             Valuation valuation,
             const LogicInfo& logicInfo,
             ProofNodeManager* pnm);
  ~TheoryBags() override;

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
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
  void postCheck(Effort level) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  TrustNode explain(TNode) override;
  Node getModelValue(TNode) override;
  std::string identify() const override { return "THEORY_BAGS"; }
  void preRegisterTerm(TNode node) override;
  TrustNode expandDefinition(Node n) override;
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
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;

   private:
    TheoryBags& d_theory;
  };

  /** The state of the bags solver at full effort */
  SolverState d_state;
  /** The inference manager */
  InferenceManager d_im;
  /** Instance of the above class */
  NotifyClass d_notify;
  /** Statistics for the theory of bags. */
  BagsStatistics d_statistics;
  /** The theory rewriter for this theory. */
  BagsRewriter d_rewriter;

  void eqNotifyNewClass(TNode t);
  void eqNotifyMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
}; /* class TheoryBags */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_BAGS_H */
