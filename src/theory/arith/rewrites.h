/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type for rewrites for arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITES_H
#define CVC5__THEORY__ARITH__REWRITES_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * Types of rewrites used by arithmetic
 */
enum class Rewrite : uint32_t
{
  NONE,
  // constant evaluation
  CONST_EVAL,
  // (mod x c) replaced by total (mod x c) if c != 0
  MOD_TOTAL_BY_CONST,
  // (div x c) replaced by total (div x c) if c != 0
  DIV_TOTAL_BY_CONST,
  // Total versions choose arbitrary values for 0 denominator:
  // (div x 0) ---> 0
  // (mod x 0) ---> 0
  DIV_MOD_BY_ZERO,
  // (mod x 1) --> 0
  MOD_BY_ONE,
  // (div x 1) --> x
  DIV_BY_ONE,
  // (div x (- c)) ---> (- (div x c))
  // (mod x (- c)) ---> (mod x c)
  DIV_MOD_PULL_NEG_DEN,
  // (mod (mod x c) c) --> (mod x c)
  MOD_OVER_MOD,
  // (mod (op ... (mod x c) ...) c) ---> (mod (op ... x ...) c) where
  // op is one of { NONLINEAR_MULT, MULT, ADD }.
  MOD_CHILD_MOD,
  // (div (mod x c) c) --> 0
  DIV_OVER_MOD,
  // (to_int c) --> floor(c), (is_int c) --> true iff c is int
  INT_EXT_CONST,
  // (to_int t) --> t, (is_int t) ---> true if t is int
  INT_EXT_INT,
  // (to_int real.pi) --> 3, (is_int real.pi) ---> false
  INT_EXT_PI,
  // (to_int (to_real x)) --> (to_int x), (is_int (to_real x)) --> (is_int x)
  INT_EXT_TO_REAL,
  // E.g. (<= (bv2nat x) N) -->
  //      (ite (>= N 2^w) true (ite (< N 0) false (bvule x ((_ int2bv w) N))
  // where N is a constant and w is the bitwidth of the type of x.
  INEQ_BV_TO_NAT_ELIM
};

/**
 * Converts an rewrite to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param r The rewrite
 * @return The name of the rewrite
 */
const char* toString(Rewrite r);

/**
 * Writes an rewrite name to a stream.
 *
 * @param out The stream to write to
 * @param r The rewrite to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Rewrite r);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__REWRITES_H */
