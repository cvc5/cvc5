/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of term context utilities.
 */

#include "expr/term_context.h"

#include "expr/node_algorithm.h"
#include "theory/theory.h"

namespace cvc5::internal {

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
  return theory::kindToTheoryId(k) != theory::THEORY_BOOL && k != Kind::EQUAL
         && k != Kind::SEP_STAR && k != Kind::SEP_WAND && k != Kind::SEP_LABEL
         && k != Kind::BITVECTOR_EAGER_ATOM;
}

uint32_t InQuantTermContext::initialValue() const { return 0; }

uint32_t InQuantTermContext::computeValue(TNode t,
                                          uint32_t tval,
                                          size_t index) const
{
  return t.isClosure() ? 1 : tval;
}

uint32_t InQuantTermContext::getValue(bool inQuant) { return inQuant ? 1 : 0; }

bool InQuantTermContext::inQuant(uint32_t val, bool& inQuant)
{
  return val == 1;
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
    case Kind::AND:
    case Kind::OR:
    case Kind::SEP_STAR:
      // polarity preserved
      return tval;
    case Kind::IMPLIES:
      // first child reverses, otherwise we preserve
      return index == 0 ? (tval == 0 ? 0 : (3 - tval)) : tval;
    case Kind::NOT:
      // polarity reversed
      return tval == 0 ? 0 : (3 - tval);
    case Kind::ITE:
      // head has no polarity, branches preserve
      return index == 0 ? 0 : tval;
    case Kind::FORALL:
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
  hasPol = val != 0;
  pol = val == 2;
}

uint32_t TheoryLeafTermContext::initialValue() const { return 0; }

uint32_t TheoryLeafTermContext::computeValue(TNode t,
                                             uint32_t tval,
                                             size_t index) const
{
  return theory::Theory::isLeafOf(t, d_theoryId) ? 1 : tval;
}
uint32_t BoolSkeletonTermContext::initialValue() const { return 0; }

uint32_t BoolSkeletonTermContext::computeValue(TNode t,
                                               uint32_t tval,
                                               size_t child) const
{
  if (tval == 0)
  {
    if (!expr::isBooleanConnective(t))
    {
      return 1;
    }
    return 0;
  }
  return 1;
}

uint32_t WithinKindTermContext::initialValue() const { return 0; }

uint32_t WithinKindTermContext::computeValue(TNode t,
                                             uint32_t tval,
                                             size_t index) const
{
  if (tval == 0)
  {
    if (t.getKind() == d_kind)
    {
      return 1;
    }
    return 0;
  }
  return 1;
}

}  // namespace cvc5::internal
