/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite fields theory.
 *
 * There is a subtheory for each prime p that handles the field Fp. Essentially
 * the common theory just multiplexes the sub-theories.
 *
 * NB: while most of FF does not build without CoCoA, this class does. So, it
 * has many ifdef blocks that throw errors without CoCoA.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__THEORY_FF_H
#define CVC5__THEORY__FF__THEORY_FF_H

#include <memory>

#include "smt/logic_exception.h"
#include "theory/care_pair_argument_callback.h"
#include "theory/ff/stats.h"
#include "theory/ff/sub_theory.h"
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
  /** The subtheory saves this for later (postCheck) */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  /** Lift the common polynomial root to a model */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  std::string identify() const override { return "THEORY_FF"; }
  /** preRegister this term or equality with the eq engine */
  void preRegisterWithEe(TNode node);
  /**
   * Trigers the creation of new-subtheories, and used to track the variables of
   * the polynomial ring that we will build.
   *
   * 1. Registers term with the equality engine
   * 2. Creates a new sub-theory for this term’s sort (if needed)
   * 3. Gives this term to that sub-theory
   *   * Maintains a list of all theory leaves (for the variable set X)
   */
  void preRegisterTerm(TNode node) override;
  TrustNode explain(TNode n) override;

 private:
  TheoryFiniteFieldsRewriter d_rewriter;

  /** The state of the ff solver at full effort */
  TheoryState d_state;

  /** The inference manager */
  TheoryInferenceManager d_im;

  /** Manages notifications from our equality engine */
  TheoryEqNotifyClass d_eqNotify;

#ifdef CVC5_USE_COCOA
  /**
   * Map from field types to sub-theories.
   */
  std::unordered_map<TypeNode, SubTheory> d_subTheories;
#endif /* CVC5_USE_COCOA */

  std::unique_ptr<FfStatistics> d_stats;
}; /* class TheoryFiniteFields */

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__THEORY_FF_H */
