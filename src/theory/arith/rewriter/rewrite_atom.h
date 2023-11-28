/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for rewriting atoms in the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__REWRITE_ATOM_H
#define CVC5__THEORY__ARITH__REWRITER__REWRITE_ATOM_H

#include <optional>

#include "expr/node.h"
#include "theory/arith/rewriter/addition.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace rewriter {

/**
 * Tries to evaluate the given relation. Returns std::nullopt if either left
 * or right is not a value (constant or a real algebraic number).
 * Assumes rel to be a relational operator, i.e. one of <,<=,=,!=,>=,>.
 */
std::optional<bool> tryEvaluateRelation(Kind rel, TNode left, TNode right);

/**
 * Tries to evaluate a reflexive relation. Returns std::nullopt if the atom
 * is either not a relational operator or not reflexive (i.e. the two terms are
 * not identical).
 * Assumes atom to be a relational operator, i.e. one of <,<=,=,!=,>=,>.
 */
std::optional<bool> tryEvaluateRelationReflexive(Kind rel,
                                                 TNode left,
                                                 TNode right);

/**
 * Build a node `(kind left right)`. If negate is true, it returns the negation
 * of this as `(not (kind left right))`. Before doing so, try to evaluate it to
 * true or false using the tryEvaluateRelation method.
 */
Node buildRelation(Kind kind, Node left, Node right, bool negate = false);

/**
 * Build an integer equality from the given sum. The result is equivalent to the
 * sum being equal to zero. We first normalize the non-constant coefficients to
 * integers (using GCD and LCM). If the coefficient is non-integral after that,
 * the result is false. We then put the term with minimal absolute coefficient
 * to the left side of the equality and make its coefficient positive.
 * The sum is taken as rvalue as it is modified in the process.
 */
Node buildIntegerEquality(Sum&& sum);

/**
 * Build a real equality from the given sum. The result is equivalent to the sum
 * being equal to zero. We first extract the leading term and normalize its
 * coefficient to be plus or minus one. The result is the (normalized) leading
 * term being equal to the rest of the sum.
 * The sum is taken as rvalue as it is modified in the process.
 */
Node buildRealEquality(Sum&& sum);

/**
 * Build an integer inequality from the given sum. The result is equivalent to
 * `(k sum 0)`. We first normalize the non-constant coefficients to integers
 * (using GCD and LCM), tighten the inequality if possible and turn it into a
 * weak inequality. The result is the resulting sum compared with the constant
 * where the overall inequalit is possibly negated.
 * The sum is taken as rvalue as it is modified in the process.
 */
Node buildIntegerInequality(Sum&& sum, Kind k);

/**
 * Build a real inequality from the given sum. The result is equivalent to
 * `(k sum 0)`. We normalize the leading coefficient to be one or minus one.
 * The result is the resulting sum compared with the constant.
 * The sum is taken as rvalue as it is modified in the process.
 */
Node buildRealInequality(Sum&& sum, Kind k);

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
