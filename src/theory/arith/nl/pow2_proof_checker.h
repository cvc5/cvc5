/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pow2 proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__POW2_PROOF_CHECKER_H
#define CVC5__THEORY__ARITH__NL__POW2_PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

/**
 * A checker for the axioms emitted by Pow2Solver.
 */
class Pow2ProofRuleChecker : public ProofRuleChecker
{
 public:
  Pow2ProofRuleChecker(NodeManager* nm);

  /** Register all rules owned by this rule checker in pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(ProofRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
