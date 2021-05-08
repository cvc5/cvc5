/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "expr/proof_checker.h"

namespace cvc5 {
namespace theory {
namespace arith {

/** A checker for arithmetic reasoning in proofs */
class ArithProofRuleChecker : public ProofRuleChecker
{
 public:
  ArithProofRuleChecker() {}
  ~ArithProofRuleChecker() {}

  /** Register all rules owned by this rule checker into pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__PROOF_CHECKER_H */
