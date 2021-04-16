/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CAD proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__CAD__PROOF_CHECKER_H
#define CVC5__THEORY__ARITH__NL__CAD__PROOF_CHECKER_H

#include "expr/node.h"
#include "expr/proof_checker.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/**
 * A checker for CAD proofs
 *
 * This proof checker takes care of the two CAD proof rules ARITH_NL_CAD_DIRECT
 * and ARITH_NL_CAD_RECURSIVE. It does not do any actual proof checking yet, but
 * considers them to be trusted rules.
 */
class CADProofRuleChecker : public ProofRuleChecker
{
 public:
  CADProofRuleChecker() {}
  ~CADProofRuleChecker() {}

  /** Register all rules owned by this rule checker in pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__STRINGS__PROOF_CHECKER_H */
