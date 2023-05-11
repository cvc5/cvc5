/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include "expr/node.h"
#include "theory/quantifiers/proof_checker.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersMacros;

class TheoryQuantifiers : public Theory {
 public:
  TheoryQuantifiers(Env& env, OutputChannel& out, Valuation valuation);
  ~TheoryQuantifiers();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /** finish initialization */
  void finishInit() override;
  /** needs equality engine */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  //--------------------------------- end initialization

  void preRegisterTerm(TNode n) override;
  void presolve() override;
  /**
   * Preprocess assert, which solves for quantifier macros when enabled.
   */
  PPAssertStatus ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions) override;
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  std::string identify() const override
  {
    return std::string("TheoryQuantifiers");
  }

 private:
  /** The theory rewriter for this theory. */
  QuantifiersRewriter d_rewriter;
  /** The proof rule checker */
  QuantifiersProofRuleChecker d_checker;
  /** The quantifiers state */
  QuantifiersState d_qstate;
  /** The quantifiers registry */
  QuantifiersRegistry d_qreg;
  /** The term registry */
  TermRegistry d_treg;
  /** The quantifiers inference manager */
  QuantifiersInferenceManager d_qim;
  /** The quantifiers engine, which lives here */
  std::unique_ptr<QuantifiersEngine> d_qengine;
  /** The quantifiers macro module, used for ppAssert. */
  std::unique_ptr<QuantifiersMacros> d_qmacros;
};/* class TheoryQuantifiers */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */
