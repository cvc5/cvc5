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
  CONST_EVAL,
  MOD_TOTAL_BY_CONST,
  DIV_TOTAL_BY_CONST,
  DIV_MOD_BY_ZERO,
  MOD_BY_ONE,
  DIV_BY_ONE,
  DIV_MOD_PULL_NEG_DEN,
  MOD_OVER_MOD,
  MOD_CHILD_MOD,
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
