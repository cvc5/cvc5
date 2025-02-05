/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * parsing structured field terms.
 *
 * NB: many functions in this file return an empty std::optional if parsing
 * fails.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__PARSE_H
#define CVC5__THEORY__FF__PARSE_H

// external includes

// std includes
#include <optional>
#include <queue>
#include <unordered_map>

// internal includes
#include "base/output.h"
#include "expr/attribute.h"
#include "expr/node.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace parse {

/**
 * Detect whether this node constrains a variable to 0.
 *
 * @param fact a node asserted to FF
 */
bool zeroConstraint(const Node& fact);

/**
 * Detect whether this node constrains a variable to 1.
 *
 * @param fact a node asserted to FF
 */
bool oneConstraint(const Node& fact);

/**
 * Detect whether this node is a bit-constraint (sets a variable to 0 or 1).
 *
 * Examples of such nodes include:
 *
 *    * `x * x = x`
 *    * `x * x - x = 0`
 *    * `x * (x - 1) = 0`
 *
 * But note that this function will parse any field node of depth <= 5 that is
 * semantically equivalent to the polynomial x^2-x.
 *
 * @param fact a node asserted to FF
 * @return a variable that is bit-constrained by this fact, if this fact is a
 *         bit constraint;
 *         returns an empty optional if this is not detectably a bit constraint
 */
std::optional<Node> bitConstraint(const Node& fact);

/**
 * Detect whether this node is a variable multiplied by a scalar:
 *
 *    * k * X
 *    * X * k
 *    * X
 *    * -X
 *
 * @param t a potential linear monomial
 * @return the variable and scalar;
 *         returns an empty optional if this is not a (syntatic) linear monomial
 */
std::optional<std::pair<Node, FiniteFieldValue>> linearMonomial(const Node& t);

/**
 * Extract linear monomials. That is, given a sum S = x + 4y + 6 + x*x + x*y,
 * it would return [(x, 1), (y, 4)] and [6, x*x, x*y].
 *
 * @param t a sum with (potential) linear monomials
 * @return the linear monomials
 *         everything else in the sum
 */
std::optional<std::pair<std::vector<std::pair<Node, FiniteFieldValue>>,
                        std::vector<Node>>>
extractLinearMonomials(const Node& t);

/**
 * Given a sum s1 + ... + sN, extract sub-sums of form k * (x0 + 2*x1 + 4*x2 +
 * ... 2^I*xI), preferring xJ that are in the given set `bits`.
 *
 * A caller might pass a set `bits` that contains nodes that are already known
 * to be bit-constrained (i.e., have a value in {0, 1}).
 *
 * @param t a potential bitsum
 * @param bits node set containing bit-constrained vars; these are prefered in
 *             bitsum extraction.
 * @return (the bitsums {(k, {xJ})}, everything else in the sum)
 *         or none if parsing fails
 */
std::optional<
    std::pair<std::vector<std::pair<FiniteFieldValue, std::vector<Node>>>,
              std::vector<Node>>>
bitSums(const Node& t, std::unordered_set<Node> bits);

/**
 * Is this a disjunctive bit constraint (or (= x 0) (= x 1))?
 *
 * @param t a fact
 * @return the var that is bit-constrained
 */
std::optional<Node> disjunctiveBitConstraint(const Node& t);

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PARSE_H */
