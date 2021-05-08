/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for cardinality classes.
 */

#include "util/cardinality_class.h"

#include <iostream>

namespace cvc5 {

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

CardinalityClass minCardinalityClass(CardinalityClass c1, CardinalityClass c2)
{
  return c1 < c2 ? c1 : c2;
}

CardinalityClass maxCardinalityClass(CardinalityClass c1, CardinalityClass c2)
{
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

}  // namespace cvc5
