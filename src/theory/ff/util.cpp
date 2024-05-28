/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * utilities
 */

#include "theory/ff/util.h"

// external includes
#ifdef CVC5_USE_COCOA
#include <CoCoA/QuotientRing.H>
#endif /* CVC5_USE_COCOA */

// std includes

// internal includes
#include "theory/ff/cocoa_util.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

FieldObj::FieldObj(const FfSize& size)
    : d_size(size),
      d_nm(NodeManager::currentNM()),
      d_zero(d_nm->mkConst(FiniteFieldValue(0, d_size))),
      d_one(d_nm->mkConst(FiniteFieldValue(1, d_size)))
#ifdef CVC5_USE_COCOA
      ,
      d_coeffRing(CoCoA::NewZZmod(intToCocoa(d_size)))
#endif /* CVC5_USE_COCOA */
{
}

template <bool ref_count>
Node FieldObj::mkAdd(const std::vector<NodeTemplate<ref_count>>& summands)
{
  if (summands.empty())
  {
    return d_zero;
  }
  else if (summands.size() == 1)
  {
    return summands[0];
  }
  else
  {
    return d_nm->mkNode(Kind::FINITE_FIELD_ADD, std::move(summands));
  }
}

template <bool ref_count>
Node FieldObj::mkMul(const std::vector<NodeTemplate<ref_count>>& factors)
{
  if (factors.empty())
  {
    return d_one;
  }
  else if (factors.size() == 1)
  {
    return factors[0];
  }
  else
  {
    return d_nm->mkNode(Kind::FINITE_FIELD_MULT, std::move(factors));
  }
}

bool isFfLeaf(const Node& n)
{
  return n.getType().isFiniteField() && Theory::isLeafOf(n, THEORY_FF);
}

bool isFfTerm(const Node& n) { return n.getType().isFiniteField(); }

bool isFfFact(const Node& n)
{
  return (n.getKind() == Kind::EQUAL && n[0].getType().isFiniteField())
         || (n.getKind() == Kind::NOT && n[0].getKind() == Kind::EQUAL
             && n[0][0].getType().isFiniteField());
}

FfTimeoutException::FfTimeoutException(const std::string& where)
    : Exception(std::string("finite field solver timeout in ") + where)
{
}

FfTimeoutException::~FfTimeoutException() {}

bool isFfLeaf(const Node& n, const FfSize& field)
{
  return n.getType().isFiniteField() && Theory::isLeafOf(n, THEORY_FF)
         && n.getType().getFfSize() == field;
}

bool isFfTerm(const Node& n, const FfSize& field)
{
  return n.getType().isFiniteField() && n.getType().getFfSize() == field;
}

bool isFfFact(const Node& n, const FfSize& field)
{
  return (n.getKind() == Kind::EQUAL && n[0].getType().isFiniteField()
          && n[0].getType().getFfSize() == field)
         || (n.getKind() == Kind::NOT && n[0].getKind() == Kind::EQUAL
             && n[0][0].getType().isFiniteField()
             && n[0][0].getType().getFfSize() == field);
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
