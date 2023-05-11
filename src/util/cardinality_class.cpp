/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for cardinality classes.
 */

#include "util/cardinality_class.h"

#include <iostream>

namespace cvc5::internal {

const char* toString(CardinalityClass c)
{
  switch (c)
  {
    case CardinalityClass::ONE: return "ONE";
    case CardinalityClass::INTERPRETED_ONE: return "INTERPRETED_ONE";
    case CardinalityClass::FINITE: return "FINITE";
    case CardinalityClass::INTERPRETED_FINITE: return "INTERPRETED_FINITE";
    case CardinalityClass::INFINITE: return "INFINITE";
    case CardinalityClass::UNKNOWN: return "UNKNOWN";
    default: return "?CardinalityClass?";
  }
}

std::ostream& operator<<(std::ostream& out, CardinalityClass c)
{
  out << toString(c);
  return out;
}

CardinalityClass maxCardinalityClass(CardinalityClass c1, CardinalityClass c2)
{
  // If one of the classes is interpreted one and the other finite, then the
  // result should be interpreted finite: the type is finite under the
  // assumption that uninterpreted sorts have cardinality one, but infinite
  // otherwise.
  if ((c1 == CardinalityClass::INTERPRETED_ONE
       && c2 == CardinalityClass::FINITE)
      || (c1 == CardinalityClass::FINITE
          && c2 == CardinalityClass::INTERPRETED_ONE))
  {
    return CardinalityClass::INTERPRETED_FINITE;
  }
  return c1 > c2 ? c1 : c2;
}

bool isCardinalityClassFinite(CardinalityClass c, bool fmfEnabled)
{
  if (c == CardinalityClass::ONE || c == CardinalityClass::FINITE)
  {
    return true;
  }
  if (fmfEnabled)
  {
    // if finite model finding is enabled, interpreted one/finite are also
    // considered finite.
    return c == CardinalityClass::INTERPRETED_ONE
           || c == CardinalityClass::INTERPRETED_FINITE;
  }
  return false;
}

}  // namespace cvc5::internal
