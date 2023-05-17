/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Coverings proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__PROOF_CHECKER_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

/**
 * A checker for coverings proofs
 *
 * This proof checker takes care of the two coverings proof rules ARITH_NL_COVERING_DIRECT
 * and ARITH_NL_COVERING_RECURSIVE. It does not do any actual proof checking yet, but
 * considers them to be trusted rules.
 */
class CoveringsProofRuleChecker : public ProofRuleChecker
{
 public:
  CoveringsProofRuleChecker() {}
  ~CoveringsProofRuleChecker() {}

  /** Register all rules owned by this rule checker in pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__PROOF_CHECKER_H */
