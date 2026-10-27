/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Util functions for theory FP.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__UTILS_H
#define CVC5__THEORY__FP__UTILS_H

#include <utility>

#include "expr/type_node.h"
#include "util/floatingpoint.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/roundingmode.h"

namespace cvc5::internal {
namespace theory {
namespace fp {
namespace utils {

/**
 * Get the cardinality of the given FP type node.
 * @param type The type node.
 * @return The cardinality.
 */
Integer getCardinality(const TypeNode& type);

/**
 * Check whether the node has a type that is disallowed by --fp-exp and throw
 * an exception.
 * @param n The node to check.
 */
void checkForExperimentalFloatingPointType(const Node& n);

/**
 * Compute the exact lower boundary of the rounding cell of a finite
 * floating-point value c under rounding mode rm: the rational threshold t0
 * such that for all reals x,
 *   to_fp(rm, x) >=_fp c  iff  (strict ? x > t0 : x >= t0).
 *
 * Requires that c is neither NaN nor infinite, and that the cell of c has a
 * finite lower boundary, i.e., that nextDown(c) is not -infinity.
 *
 * @param c The floating-point value whose rounding cell is considered.
 * @param rm The rounding mode.
 * @return The threshold t0 and a flag that is true if the lower bound is
 *         strict.
 */
std::pair<Rational, bool> roundingCellLowerBound(const FloatingPoint& c,
                                                 RoundingMode rm);

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
#endif
