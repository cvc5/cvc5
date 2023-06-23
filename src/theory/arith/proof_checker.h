/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__PROOF_CHECKER_H
#define CVC5__THEORY__ARITH__PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/proof_checker.h"
#include "theory/arith/nl/coverings/proof_checker.h"
#include "theory/arith/nl/ext/proof_checker.h"
#include "theory/arith/nl/transcendental/proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/** A checker for arithmetic reasoning in proofs */
class ArithProofRuleChecker : public ProofRuleChecker
{
 public:
  ArithProofRuleChecker();
  ~ArithProofRuleChecker() {}

  /** Register all rules owned by this rule checker into pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
  /** The proof checker for proofs of the nlext. */
  nl::ExtProofRuleChecker d_extChecker;
  /** The proof checker for transcendental proofs */
  nl::transcendental::TranscendentalProofRuleChecker d_trChecker;
#ifdef CVC5_POLY_IMP
  /** The proof checker for coverings proofs */
  nl::coverings::CoveringsProofRuleChecker d_covChecker;
#endif
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__PROOF_CHECKER_H */
