/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * parsing structured field terms
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
 * @param fact a node asserted to FF
 * @return a variable that is bit-constrained by this fact, if this fact is a
 *         bit constraint.
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
 * @return the variable and scalar
 */
std::optional<std::pair<Node, FiniteFieldValue>> linearMonomial(const Node& t);

/**
 * Extract linear monomials.
 *
 * @param t a potential affine sum
 * @param hasOtherUses node predicate for whether there are other uses
 * @return the linear monomials
 *         everything else in the sum
 */
std::optional<std::pair<std::vector<std::pair<Node, FiniteFieldValue>>,
                        std::vector<Node>>>
extractLinearMonomials(const Node& t);

/**
 * Given a sum s1 + ... + sN, extract sub-sums of form k * (x0 + 2*x1 + 4*x2 +
 * ... 2^I*xI), preferring xJ that are in bits.
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
