/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Strings proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__PROOF_CHECKER_H
#define CVC5__THEORY__STRINGS__PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/** A checker for strings proofs */
class StringProofRuleChecker : public ProofRuleChecker
{
 public:
  StringProofRuleChecker(uint32_t alphaCard) : d_alphaCard(alphaCard) {}
  ~StringProofRuleChecker() {}

  /** Register all rules owned by this rule checker in pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
  /** cardinality of the alphabet, which impacts certain inferences */
  uint32_t d_alphaCard;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__PROOF_CHECKER_H */
