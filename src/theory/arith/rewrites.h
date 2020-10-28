/*********************                                                        */
/*! \file rewrites.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Type for rewrites for arithmetic.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__REWRITES_H
#define CVC4__THEORY__ARITH__REWRITES_H

#include <iosfwd>

namespace CVC4 {
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
  // op is one of { NONLINEAR_MULT, MULT, PLUS }.
  MOD_CHILD_MOD,
  // (div (mod x c) c) --> 0
  DIV_OVER_MOD
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
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__REWRITES_H */
