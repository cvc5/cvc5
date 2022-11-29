/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields theory
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__THEORY_FF_H
#define CVC5__THEORY__FF__THEORY_FF_H

#include <memory>

#include "smt/logic_exception.h"
#include "theory/care_pair_argument_callback.h"
#include "theory/ff/theory_ff_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class TheoryFiniteFields : public Theory
{
 public:
  /** Constructs a new instance of TheoryFiniteFields */
  TheoryFiniteFields(Env& env, OutputChannel& out, Valuation valuation);
  ~TheoryFiniteFields() override;

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
  void postCheck(Effort level) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  void computeCareGraph() override;
  TrustNode explain(TNode) override;
  Node getModelValue(TNode) override;
  std::string identify() const override { return "THEORY_FF"; }
  void preRegisterTerm(TNode node) override;
  TrustNode ppRewrite(TNode n, std::vector<SkolemLemma>& lems) override;
  PPAssertStatus ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions) override;
  void presolve() override;
  bool isEntailed(Node n, bool pol);

 private:
  TheoryFiniteFieldsRewriter d_rewriter{};

  /** The state of the ff solver at full effort */
  TheoryState d_state;

  /** The inference manager */
  TheoryInferenceManager d_im;

  /** Manages notifications from our equality engine */
  TheoryEqNotifyClass d_eqNotify;
}; /* class TheoryFiniteFields */

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__THEORY_FF_H */
