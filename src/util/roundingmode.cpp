/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
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

#include "roundingmode.h"

#include <iostream>

#include "base/check.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& os, RoundingMode rm)
{
  switch (rm)
  {
    case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
      os << "ROUND_NEAREST_TIES_TO_EVEN";
      break;
    case RoundingMode::ROUND_TOWARD_POSITIVE:
      os << "ROUND_TOWARD_POSITIVE";
      break;
    case RoundingMode::ROUND_TOWARD_NEGATIVE:
      os << "ROUND_TOWARD_NEGATIVE";
      break;
    case RoundingMode::ROUND_TOWARD_ZERO: os << "ROUND_TOWARD_ZERO"; break;
    case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
      os << "ROUND_NEAREST_TIES_TO_AWAY";
      break;
    default: Unreachable();
  }
  return os;
}

}  // namespace cvc5::internal
