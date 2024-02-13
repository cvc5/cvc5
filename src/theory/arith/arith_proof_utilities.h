/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include "proof/proof_node.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

std::vector<Node> getMacroSumUbCoeff(const std::vector<Pf>& pfs, const std::vector<Node>& coeffs);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_PROOF_UTILITIES_H */
