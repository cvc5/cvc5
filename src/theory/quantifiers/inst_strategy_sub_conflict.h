/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Subsolver conflict quantifier instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_SUB_CONFLICT_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_SUB_CONFLICT_H

#include "proof/trust_proof_generator.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * InstStrategySubConflict
 *
 * This strategy invokes a subsolver for the current set of asserted literals.
 * For example say L1 ... Ln are asserted.
 * If the call to the subsolver is unsat, it adds two kinds of lemmas:
 * (1) An "unsat core" lemma of the form ~(Li1 ... Lij) for the unsat core
 * computed by the subsolver,
 * (2) Instantiation lemmas Li => Li[t/x] for relevant instantiations of
 * quantified formulas Li, as determined by the proof.
 */
class InstStrategySubConflict : public QuantifiersModule
{
 public:
  InstStrategySubConflict(Env& env,
                          QuantifiersState& qs,
                          QuantifiersInferenceManager& qim,
                          QuantifiersRegistry& qr,
                          TermRegistry& tr);
  ~InstStrategySubConflict() {}
  /** reset round */
  void reset_round(Theory::Effort e) override;
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** identify */
  std::string identify() const override;

 private:
  /** The options for subsolver calls */
  Options d_subOptions;
  /** For lemmas */
  std::shared_ptr<TrustProofGenerator> d_tpg;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_ALL_EAGER_H */
