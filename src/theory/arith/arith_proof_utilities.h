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
 * Common functions for dealing with proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_PROOF_UTILITIES_H
#define CVC5__THEORY__ARITH__ARITH_PROOF_UTILITIES_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * Get the list of coefficients to use for an application of
 * ProofRule::MACRO_ARITH_SCALE_SUM_UB. This method ensures
 * the types of the coefficients in coeffs are appropriate for the proofs in
 * pfs. In particular, this method returns a vector of constants ret of the same
 * magnitude as coeffs. It ensures ret[i] has real type iff either coeffs[i]
 * is not integral or pfs[i] is of the form (~ t1 t2) where either t1 or t2
 * has real type.
 *
 * This method ensures we do not spuriously introduce mixed arithmetic, which
 * the proof checker for MACRO_ARITH_SCALE_SUM_UB requires.
 */
std::vector<Node> getMacroSumUbCoeff(const std::vector<Pf>& pfs,
                                     const std::vector<Node>& coeffs);

/**
 * Expand an instance of ProofRule::MACRO_ARITH_SCALE_SUM_UB.
 * This adds steps to cdp that prove the same as an application of this rule,
 * assuming that children are free assumptions.
 *
 * This method assumes that children and args are valid parameters to
 * MACRO_ARITH_SCALE_SUM_UB.
 *
 * @param children The children of MACRO_ARITH_SCALE_SUM_UB.
 * @param args The arguments of MACRO_ARITH_SCALE_SUM_UB.
 * @param cdp The proof to add steps to.
 * @return The conclusion of the proof rule.
 */
Node expandMacroSumUb(const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      CDProof* cdp);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_PROOF_UTILITIES_H */
