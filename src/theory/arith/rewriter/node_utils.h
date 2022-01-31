/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Node utilities for the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__NODE_UTILS_H
#define CVC5__THEORY__ARITH__REWRITER__NODE_UTILS_H

#include "base/check.h"
#include "expr/node.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::theory::arith::rewriter {

inline bool isAtom(TNode n)
{
  switch (n.getKind())
  {
    case Kind::LT:
    case Kind::LEQ:
    case Kind::EQUAL:
    case Kind::GEQ:
    case Kind::GT:
    case Kind::IS_INTEGER:
    case Kind::DIVISIBLE: return true;
    default: return false;
  }
}

/**
 * Check whether the given node can be rewritten to an integer node. This
 * differs from checking the node type in two major ways: we consider relational
 * operators integral if both children are integral in this sense; rational
 * constants are always integral, as they are rewritten to integers by simple
 * multiplication with their denominator.
 */
bool isIntegral(TNode n);

inline bool isRAN(TNode n)
{
  return n.getKind() == Kind::REAL_ALGEBRAIC_NUMBER;
}
inline const RealAlgebraicNumber& getRAN(TNode n)
{
  Assert(isRAN(n));
  return n.getOperator().getConst<RealAlgebraicNumber>();
}

/**
 * Check whether the parent has a child that is a constant zero. If so, return
 * this child. Otherwise, return std::nullopt. Works on any kind of iterable,
 * i.e. both a node or a vector of nodes.
 */
template <typename Iterable>
std::optional<TNode> getZeroChild(const Iterable& parent)
{
  for (const auto& node : parent)
  {
    if (node.isConst() && node.template getConst<Rational>().isZero())
    {
      return node;
    }
  }
  return {};
}

inline Node mkConst(bool value)
{
  return NodeManager::currentNM()->mkConst(value);
}
inline Node mkConst(const Integer& value)
{
  return NodeManager::currentNM()->mkConstInt(value);
}
inline Node mkConst(const Rational& value)
{
  if (value.isIntegral())
  {
    return NodeManager::currentNM()->mkConstInt(value);
  }
  return NodeManager::currentNM()->mkConstReal(value);
}
inline Node mkConst(const RealAlgebraicNumber& value)
{
  return NodeManager::currentNM()->mkRealAlgebraicNumber(value);
}

/** Make a nonlinear multiplication from the given factors */
inline Node mkNonlinearMult(const std::vector<Node>& factors)
{
  auto* nm = NodeManager::currentNM();
  switch (factors.size())
  {
    case 0: return nm->mkConstInt(Rational(1));
    case 1: return factors[0];
    default: return nm->mkNode(Kind::NONLINEAR_MULT, factors);
  }
}

}  // namespace cvc5::theory::arith::rewriter

#endif
