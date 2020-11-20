/*********************                                                        */
/*! \file roundingmode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Martin Brain, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The definition of rounding mode values.
 **/
#include "cvc4_public.h"

#ifndef CVC4__ROUNDINGMODE_H
#define CVC4__ROUNDINGMODE_H

#include <fenv.h>

namespace CVC4 {

#define CVC4_NUM_ROUNDING_MODES 5

/**
 * A concrete instance of the rounding mode sort
 */
enum CVC4_PUBLIC RoundingMode
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
struct CVC4_PUBLIC RoundingModeHashFunction
{
  inline size_t operator()(const RoundingMode& rm) const { return size_t(rm); }
}; /* struct RoundingModeHashFunction */

}  // namespace CVC4

#endif
