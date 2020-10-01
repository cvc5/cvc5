/*********************                                                        */
/*! \file term_context.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term context utilities.
 **/

#include "expr/term_context.h"

namespace CVC4 {

uint32_t TermContext::computeValueOp(TNode t, uint32_t tval) const
{
  // default is no change
  return tval;
}

uint32_t RtfTermContext::initialValue() const
{
  // by default, not in a term context or a quantifier
  return 0;
}

uint32_t RtfTermContext::computeValue(TNode t,
                                      uint32_t tval,
                                      size_t child) const
{
  if (t.isClosure())
  {
    if (tval % 2 == 0)
    {
      return tval + 1;
    }
  }
  else if (hasNestedTermChildren(t))
  {
    if (tval < 2)
    {
      return tval + 2;
    }
  }
  return tval;
}

uint32_t RtfTermContext::getValue(bool inQuant, bool inTerm)
{
  return (inQuant ? 1 : 0) + 2 * (inTerm ? 1 : 0);
}

void RtfTermContext::getFlags(uint32_t val, bool& inQuant, bool& inTerm)
{
  inQuant = val % 2 == 1;
  inTerm = val >= 2;
}

bool RtfTermContext::hasNestedTermChildren(TNode t)
{
  Kind k = t.getKind();
  // dont' worry about FORALL or EXISTS, these are part of inQuant.
  return theory::kindToTheoryId(k) != theory::THEORY_BOOL && k != kind::EQUAL
         && k != kind::SEP_STAR && k != kind::SEP_WAND && k != kind::SEP_LABEL
         && k != kind::BITVECTOR_EAGER_ATOM;
}

uint32_t PolarityTermContext::initialValue() const
{
  // by default, we have true polarity
  return 2;
}

uint32_t PolarityTermContext::computeValue(TNode t,
                                           uint32_t tval,
                                           size_t index) const
{
  switch (t.getKind())
  {
    case kind::AND:
    case kind::OR:
    case kind::SEP_STAR:
      // polarity preserved
      return tval;
    case kind::IMPLIES:
      // first child reverses, otherwise we preserve
      return index == 0 ? (tval == 0 ? 0 : (3 - tval)) : tval;
    case kind::NOT:
      // polarity reversed
      return tval == 0 ? 0 : (3 - tval);
    case kind::ITE:
      // head has no polarity, branches preserve
      return index == 0 ? 0 : tval;
    case kind::FORALL:
      // body preserves, others have no polarity.
      return index == 1 ? tval : 0;
    default:
      // no polarity
      break;
  }
  return 0;
}

uint32_t PolarityTermContext::getValue(bool hasPol, bool pol)
{
  return hasPol ? (pol ? 2 : 1) : 0;
}

void PolarityTermContext::getFlags(uint32_t val, bool& hasPol, bool& pol)
{
  hasPol = val == 0;
  pol = val == 2;
}

}  // namespace CVC4
