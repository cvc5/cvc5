/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Addition utilities for the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__ADDITION_H
#define CVC5__THEORY__ARITH__REWRITER__ADDITION_H

#include <iosfwd>
#include <map>

#include "expr/node.h"
#include "theory/arith/rewriter/ordering.h"
#include "util/real_algebraic_number.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace rewriter {

/**
 * Intermediate representation for a sum of terms, mapping monomials to their
 * multiplicities. A sum implicitly represents the expression
 *   SUM(s.second * s.first for s in sum)
 * Using a map allows to easily check whether a monomial is already present and
 * then merge two terms (i.e. add their multiplicities). We use a std::map with
 * a proper comparator (instead of std::unordered_map) to allow easy
 * identification of the leading term. As we need to sort the terms anyway when
 * constructing a node, a std::unordered_map may only be faster if we experience
 * a lot of nullification (and thus paying the logarithmic overhead when working
 * with the map, but not having it when sorting in the end). Usually, though,
 * this saves us additional memory allocations for sorting the terms as it is
 * done in-place instead of copying the result out of the std::unordered_map
 * into a sortable container.
 */
using Sum = std::map<Node, RealAlgebraicNumber, TermComparator>;

/**
 * Print a sum. Does not use a particularly useful syntax and is thus only meant
 * for debugging.
 */
std::ostream& operator<<(std::ostream& os, const Sum& sum);

/**
 * Check whether the given sum can be rewritten as an integer expression. This
 * differs from checking the node type in a major way: rational
 * constants are always integral, as they are rewritten to integers by simple
 * multiplication with their denominator.
 */
bool isIntegral(const Sum& sum);

/**
 * Add the arithmetic term `n` to the given sum. If negate is true, actually add
 * `-n`. If `n` is itself a sum, it automatically flattens it into `sum` (though
 * it should not be a deeply nested sum, as it simply recurses). Otherwise, `n`
 * is treated as a single summand, that is a (possibly unary) product.
 * It does not consider sums within the product.
 */
void addToSum(Sum& sum, TNode n, bool negate = false);

/**
 * Evaluates the sum object (mapping monomials to their multiplicities) into a
 * single node (of kind `ADD`, unless the sum has less than two summands).
 */
Node collectSum(const Sum& sum);

/**
 * Distribute a multiplication over one or more additions. The multiplication
 * is given as the list of its factors. Though this method also works if none
 * of these factors is an addition, there is no point of calling this method
 * in this case. The result is the resulting sum after expanding the product
 * and pushing the multiplication inside the addition.
 *
 * The method maintains a `sum` as a mapping from Node to RealAlgebraicNumber.
 * The nodes can be understood as monomials, or generally non-value parts of
 * the product, while the real algebraic numbers are the multiplicities of these
 * monomials or products. This allows to combine summands with identical
 * monomials immediately and avoid a potential blow-up.
 */
Node distributeMultiplication(const std::vector<TNode>& factors);

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
