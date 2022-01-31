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
 * Utilits for rewriting atoms in the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__REWRITE_ATOM_H
#define CVC5__THEORY__ARITH__REWRITER__REWRITE_ATOM_H

#include <optional>

#include "base/check.h"
#include "expr/node.h"
#include "theory/arith/rewriter/addition.h"

namespace cvc5::theory::arith::rewriter {

/**
 * Evaluate the given relation based on values l and r. Expects that the
 * relational operators `operator<(L,R)`, `operator==(L,R)`, etc are defined.
 */
template <typename L, typename R>
bool evaluateRelation(Kind rel, const L& l, const R& r)
{
  switch (rel)
  {
    case Kind::LT: return l < r;
    case Kind::LEQ: return l <= r;
    case Kind::EQUAL: return l == r;
    case Kind::DISTINCT: return l != r;
    case Kind::GEQ: return l >= r;
    case Kind::GT: return l > r;
    default: Unreachable(); return false;
  }
}

/**
 * Tries to evaluate the given relation. Returns std::nullopt if either left
 * or right is not a value (constant or a real algebraic number).
 */
std::optional<bool> tryEvaluateRelation(Kind rel, TNode left, TNode right)
{
  if (left.isConst())
  {
    const Rational& l = left.getConst<Rational>();
    if (right.isConst())
    {
      const Rational& r = right.getConst<Rational>();
      return evaluateRelation(rel, l, r);
    }
    else if (right.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      const RealAlgebraicNumber& r =
          right.getOperator().getConst<RealAlgebraicNumber>();
      return evaluateRelation(rel, l, r);
    }
  }
  else if (left.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    const RealAlgebraicNumber& l =
        left.getOperator().getConst<RealAlgebraicNumber>();
    if (right.isConst())
    {
      const Rational& r = right.getConst<Rational>();
      return evaluateRelation(rel, l, r);
    }
    else if (right.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
    {
      const RealAlgebraicNumber& r =
          right.getOperator().getConst<RealAlgebraicNumber>();
      return evaluateRelation(rel, l, r);
    }
  }
  return {};
}

/**
 * Tries to evaluate a reflexive relation. Returns std::nullopt if the atom
 * is either not a relational operator or not reflexive (i.e. the two terms are
 * not identical).
 */
std::optional<bool> tryEvaluateRelationReflexive(TNode atom)
{
  if (atom.getNumChildren() == 2 && atom[0] == atom[1])
  {
    switch (atom.getKind())
    {
      case Kind::LT: return false;
      case Kind::LEQ: return true;
      case Kind::EQUAL: return true;
      case Kind::DISTINCT: return false;
      case Kind::GEQ: return true;
      case Kind::GT: return false;
      default:;
    }
  }
  return {};
}

/**
 * Build a node `(kind left right)`. If negate is true, it returns the negation
 * of this as `(not (kind left right))`. Before doing so, try to evaluate it to
 * true or false using the tryEvaluateRelation method.
 */
Node buildRelation(Kind kind, Node left, Node right, bool negate = false)
{
  if (auto response = tryEvaluateRelation(kind, left, right); response)
  {
    return mkConst(*response != negate);
  }
  if (negate)
  {
    return NodeManager::currentNM()->mkNode(kind, left, right).notNode();
  }
  return NodeManager::currentNM()->mkNode(kind, left, right);
}

/**
 * Build an integer equality from the given summands. The result is equivalent
 * to the sum of the summands equal to zero.
 * We first normalize the non-constant coefficients to integers (using GCD and
 * LCM). If the coefficient is non-integral after that, the result is false.
 * We then put the term with minimal absolute coefficient to the left side of
 * the equality and make its coefficient positive.
 */
Node buildIntegerEquality(Sum& sum)
{
  normalize::GCDLCM(sum);

  const auto& constant = *sum.begin();
  if (constant.first.isConst())
  {
    Assert(constant.second.isRational());
    if (!constant.second.toRational().isIntegral())
    {
      return mkConst(false);
    }
  }

  auto minabscoeff = removeMinAbsCoeff(sum);
  if (sgn(minabscoeff.second) < 0)
  {
    // move minabscoeff goes to the right and switch lhs and rhs
    minabscoeff.second = -minabscoeff.second;
  }
  else
  {
    // move the sum to the right
    for (auto& s : sum) s.second = -s.second;
  }
  Node left = mkMultTerm(minabscoeff.second, minabscoeff.first);

  return buildRelation(Kind::EQUAL, left, collectSum(sum));
}

/**
 * Build a real equality from the given summands. The result is equivalent to
 * the sum of the summands equal to zero. We first extract the leading term and
 * normalize its coefficient to be plus or minus one. The result is the
 * (normalized) leading term being equal to the rest of the sum.
 */
Node buildRealEquality(Sum& sum)
{
  auto lterm = removeLTerm(sum);
  if (isZero(lterm.second))
  {
    return buildRelation(
        Kind::EQUAL, mkConst(Integer(0)), collectSum(sum));
  }
  RealAlgebraicNumber lcoeff = -lterm.second;
  for (auto& s : sum)
  {
    s.second = s.second / lcoeff;
  }
  return buildRelation(Kind::EQUAL, lterm.first, collectSum(sum));
}

Node buildIntegerInequality(Sum& sum, Kind k)
{
  bool negate = normalize::GCDLCM(sum, true);

  if (negate)
  {
    k = (k == Kind::GEQ) ? Kind::GT : Kind::GEQ;
  }

  RealAlgebraicNumber constant = removeConstant(sum);
  Assert(constant.isRational());
  Rational rhs = -constant.toRational();

  if (rhs.isIntegral() && k == Kind::GT)
  {
    rhs += 1;
  }
  else
  {
    rhs = rhs.ceiling();
  }
  auto* nm = NodeManager::currentNM();
  return buildRelation(
      Kind::GEQ, collectSum(sum), nm->mkConstInt(rhs), negate);
}

Node buildRealInequality(Sum& sum, Kind k)
{
  normalize::LCoeffAbsOne(sum);
  Node rhs = mkConst(-removeConstant(sum));
  return buildRelation(k, collectSum(sum), rhs);
}

}  // namespace cvc5::theory::arith::rewriter

#endif
