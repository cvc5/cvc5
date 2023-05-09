/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Boolean proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BOOLEANS__PROOF_CHECKER_H
#define CVC5__THEORY__BOOLEANS__PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace booleans {

/** A checker for boolean reasoning in proofs */
class BoolProofRuleChecker : public ProofRuleChecker
{
 public:
  BoolProofRuleChecker() {}
  ~BoolProofRuleChecker() {}

  /** Register all rules owned by this rule checker into pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BOOLEANS__PROOF_CHECKER_H */
