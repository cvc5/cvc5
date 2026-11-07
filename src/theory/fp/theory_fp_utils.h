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
 * The lower boundary of the set of reals that convert to at least a given
 * floating-point value, see roundingCellLowerBound().
 */
struct RoundingCellLowerBound
{
  /** The kind of the boundary. */
  enum class Kind
  {
    /** The set is bounded below by d_bound. */
    BOUNDED,
    /** The set is all of the reals. */
    ALL,
    /** The set is empty. */
    NONE,
  };
  /** The kind of this boundary. */
  Kind d_kind = Kind::BOUNDED;
  /** The boundary, only meaningful if d_kind is BOUNDED. */
  Rational d_bound = Rational();
  /** True if d_bound is excluded, only meaningful if d_kind is BOUNDED. */
  bool d_strict = false;
};

/**
 * Compute the exact lower boundary of the set of reals that convert to at
 * least a given floating-point value c under rounding mode rm,
 *   S(c, rm) = { x in R | to_fp(rm, x) >=_fp c },
 * which is upwards closed since rounding is monotone. If S(c, rm) is bounded
 * below, the result is the rational threshold t0 and a strictness flag such
 * that for all reals x,
 *   to_fp(rm, x) >=_fp c  iff  (strict ? x > t0 : x >= t0),
 * i.e., t0 is the lower boundary of the rounding cell of c. Otherwise the
 * result indicates that S(c, rm) is all of the reals or that it is empty.
 *
 * The degenerate cases occur at the extremes of the format: S(c, rm) is all of
 * the reals if c is -infinity, and if c is the smallest finite value of its
 * format under the rounding modes that saturate towards it rather than
 * overflowing to -infinity. It is empty if c is +infinity under the rounding
 * modes that saturate towards the largest finite value.
 *
 * Note that >=_fp identifies -zero and +zero, and thus so does S(c, rm).
 *
 * Requires that c is not NaN.
 *
 * @param c The floating-point value considered.
 * @param rm The rounding mode.
 * @return The lower boundary of S(c, rm).
 */
RoundingCellLowerBound roundingCellLowerBound(const FloatingPoint& c,
                                              RoundingMode rm);

}  // namespace utils
}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
#endif
