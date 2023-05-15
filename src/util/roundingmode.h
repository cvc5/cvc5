/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The definition of rounding mode values.
 */
#include "cvc5_public.h"

#ifndef CVC5__ROUNDINGMODE_H
#define CVC5__ROUNDINGMODE_H

#include <fenv.h>

#include <iosfwd>

namespace cvc5::internal {

#define CVC5_NUM_ROUNDING_MODES 5

/**
 * A concrete instance of the rounding mode sort
 */
enum class RoundingMode
{
  ROUND_NEAREST_TIES_TO_EVEN = FE_TONEAREST,
  ROUND_TOWARD_POSITIVE = FE_UPWARD,
  ROUND_TOWARD_NEGATIVE = FE_DOWNWARD,
  ROUND_TOWARD_ZERO = FE_TOWARDZERO,
  // Initializes this to the diagonalization of the 4 other values.
  ROUND_NEAREST_TIES_TO_AWAY =
      (((~FE_TONEAREST) & 0x1) | ((~FE_UPWARD) & 0x2) | ((~FE_DOWNWARD) & 0x4)
       | ((~FE_TOWARDZERO) & 0x8))
}; /* enum RoundingMode */

/**
 * Hash function for rounding mode values.
 */
struct RoundingModeHashFunction
{
  inline size_t operator()(const RoundingMode& rm) const { return size_t(rm); }
}; /* struct RoundingModeHashFunction */

std::ostream& operator<<(std::ostream& os, RoundingMode s);

}  // namespace cvc5::internal

#endif
