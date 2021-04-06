/*********************                                                        */
/*! \file cardinality_class.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for cardinality classes
 **/

#include "expr/cardinality_class.h"

#include "expr/type_node.h"

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
    default: return "?CardinalityClass?";
  }
}

std::ostream& operator<<(std::ostream& out, CardinalityClass c)
{
  out << toString(c);
  return out;
}

CardinalityClass getCardinalityClass(TypeNode tn)
{
  if (!tn.isFinite(true))
  {
    return CardinalityClass::INFINITE;
  }
  if (!tn.isFinite(false))
  {
    return CardinalityClass::INTERPRETED_FINITE;
  }
  if (!tn.isOne(true))
  {
    return CardinalityClass::FINITE;
  }
  else if (!tn.isOne(false))
  {
    return CardinalityClass::INTERPRETED_ONE;
  }
  return CardinalityClass::ONE;
}

CardinalityClass minCardinalityClass(CardinalityClass c1, CardinalityClass c2)
{
  return c1 < c2 ? c1 : c2;
}

CardinalityClass maxCardinalityClass(CardinalityClass c1, CardinalityClass c2)
{
  return c1 > c2 ? c1 : c2;
}

}  // namespace cvc5
