/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for rewriting atoms in the arithmetic rewriter.
 */

#include "theory/arith/rewriter/rewrite_atom.h"

#include "base/check.h"
#include "theory/arith/rewriter/node_utils.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace rewriter {

namespace {

/**
 * Evaluate the given relation based on values l and r. Expects that the
 * relational operators `operator<(L,R)`, `operator==(L,R)`, etc are defined.
 */
template <typename L>
bool evaluateRelation(Kind rel, const L& l, const L& r)
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

auto getLTermIt(Sum& sum)
{
  auto ltermit = sum.begin();
  if (ltermit->first.isConst())
  {
    ++ltermit;
  }
  return ltermit;
}

auto& getLTerm(Sum& sum)
{
  Assert(getLTermIt(sum) != sum.end());
  return *getLTermIt(sum);
}

/**
 * Normalize the sum, making the leading coefficient to be one or minus one.
 */
void normalizeLCoeffAbsOne(Sum& sum)
{
  if (sum.empty()) return;
  if (sum.size() == 1)
  {
    auto& front = *sum.begin();
    // Trivial if there is only one summand
    front.second = Integer(front.second.sgn() > 0 ? 1 : -1);
    return;
  }
  // LCoeff is first coefficient of non-constant monomial
  RealAlgebraicNumber lcoeff = getLTerm(sum).second;
  ;
  if (lcoeff.sgn() < 0)
  {
    lcoeff = -lcoeff;
  }
  if (lcoeff.isOne()) return;
  for (auto& s : sum)
  {
    s.second = s.second / lcoeff;
  }
}

/**
 * Normalize the sum, making all coefficients integral and their gcd one.
 * If followLCoeffSign is true, the leading coefficient is made positive,
 * possibly negating all other coefficients. If this is the case return true to
 * indicate that the relational operator needs to be negated.
 * Otherwise return false.
 */
bool normalizeGCDLCM(Sum& sum, bool followLCoeffSign = false)
{
  if (sum.empty()) return false;
  Integer denLCM(1);
  Integer numGCD;
  auto it = sum.begin();
  if (!it->first.isConst())
  {
    Rational r = it->second.toRational();
    denLCM = r.getDenominator();
    numGCD = r.getNumerator().abs();
  }
  ++it;
  for (; it != sum.end(); ++it)
  {
    if (it->first.isConst()) continue;
    Assert(it->second.isRational());
    Rational r = it->second.toRational();
    denLCM = denLCM.lcm(r.getDenominator());
    if (numGCD.isZero())
      numGCD = r.getNumerator().abs();
    else
      numGCD = numGCD.gcd(r.getNumerator().abs());
  }
  if (numGCD.isZero()) return false;
  Rational mult(denLCM, numGCD);

  bool negate = false;
  if (followLCoeffSign)
  {
    if (getLTerm(sum).second.sgn() < 0)
    {
      negate = true;
      mult = -mult;
    }
  }

  for (auto& s : sum)
  {
    s.second *= mult;
  }
  return negate;
}

std::pair<Node, RealAlgebraicNumber> removeMinAbsCoeff(NodeManager* nm,
                                                       Sum& sum)
{
  auto minit = getLTermIt(sum);
  for (auto it = minit; it != sum.end(); ++it)
  {
    if (it->first.isConst()) continue;
    if (it->second.toRational().absCmp(minit->second.toRational()) < 0)
    {
      minit = it;
    }
  }
  if (minit == sum.end())
  {
    return std::make_pair(mkConst(nm, Integer(1)), Integer(0));
  }
  Assert(minit != sum.end());
  auto res = *minit;
  sum.erase(minit);
  return res;
}

RealAlgebraicNumber removeConstant(Sum& sum)
{
  RealAlgebraicNumber res;
  if (!sum.empty())
  {
    auto constantit = sum.begin();
    if (constantit->first.isConst())
    {
      Assert(constantit->first.getConst<Rational>().isOne());
      res = constantit->second;
      sum.erase(constantit);
    }
  }
  return res;
}

std::pair<Node, RealAlgebraicNumber> removeLTerm(NodeManager* nm, Sum& sum)
{
  auto it = getLTermIt(sum);
  if (it == sum.end())
  {
    return std::make_pair(mkConst(nm, Integer(1)), Integer(0));
  }
  Assert(it != sum.end());
  auto res = *it;
  sum.erase(it);
  return res;
}

}  // namespace

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
      return evaluateRelation(rel, RealAlgebraicNumber(l), r);
    }
  }
  else if (left.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    const RealAlgebraicNumber& l =
        left.getOperator().getConst<RealAlgebraicNumber>();
    if (right.isConst())
    {
      const Rational& r = right.getConst<Rational>();
      return evaluateRelation(rel, l, RealAlgebraicNumber(r));
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

std::optional<bool> tryEvaluateRelationReflexive(Kind rel,
                                                 TNode left,
                                                 TNode right)
{
  if (left == right)
  {
    switch (rel)
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

Node buildRelation(Kind kind, Node left, Node right, bool negate)
{
  if (auto response = tryEvaluateRelation(kind, left, right); response)
  {
    return mkConst(left.getNodeManager(), *response != negate);
  }
  if (negate)
  {
    return NodeManager::mkNode(kind, left, right).notNode();
  }
  return NodeManager::mkNode(kind, left, right);
}

Node buildIntegerEquality(NodeManager* nm, Sum&& sum)
{
  Trace("arith-rewriter") << "building integer equality from " << sum
                          << std::endl;
  normalizeGCDLCM(sum);

  Trace("arith-rewriter::debug") << "\tnormalized to " << sum << std::endl;

  const auto& constant = *sum.begin();
  if (constant.first.isConst())
  {
    Assert(constant.second.isRational());
    if (!constant.second.toRational().isIntegral())
    {
      Trace("arith-rewriter::debug")
          << "\thas non-integer constant, thus false" << std::endl;
      return mkConst(nm, false);
    }
  }

  auto minabscoeff = removeMinAbsCoeff(nm, sum);
  Trace("arith-rewriter::debug") << "\tremoved min abs coeff " << minabscoeff
                                 << ", left with " << sum << std::endl;
  if (minabscoeff.second.sgn() < 0)
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

  Trace("arith-rewriter::debug")
      << "\tbuilding " << left << " = " << sum << std::endl;

  Node rhs = collectSum(nm, sum);
  Assert(left.getType().isInteger());
  Assert(rhs.getType().isInteger());
  return buildRelation(Kind::EQUAL, left, rhs);
}

Node buildRealEquality(NodeManager* nm, Sum&& sum)
{
  Trace("arith-rewriter") << "building real equality from " << sum << std::endl;
  auto lterm = removeLTerm(nm, sum);
  if (lterm.second.isZero())
  {
    return buildRelation(
        Kind::EQUAL, mkConst(nm, Integer(0)), collectSum(nm, sum));
  }
  RealAlgebraicNumber lcoeff = -lterm.second;
  for (auto& s : sum)
  {
    s.second = s.second / lcoeff;
  }
  // Must ensure real for both sides. This may change one but not both
  // terms.
  Node lhs = lterm.first;
  lhs = ensureReal(lhs);
  Node rhs = collectSum(nm, sum);
  rhs = ensureReal(rhs);
  Assert(lhs.getType().isReal() || lhs.getType().isFullyAbstract());
  Assert(rhs.getType().isReal() || rhs.getType().isFullyAbstract());
  return buildRelation(Kind::EQUAL, lhs, rhs);
}

Node buildIntegerInequality(NodeManager* nm, Sum&& sum, Kind k)
{
  Trace("arith-rewriter") << "building integer inequality from " << sum
                          << std::endl;
  bool negate = normalizeGCDLCM(sum, true);

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
  return buildRelation(
      Kind::GEQ, collectSum(nm, sum), nm->mkConstInt(rhs), negate);
}

Node buildRealInequality(NodeManager* nm, Sum&& sum, Kind k)
{
  Trace("arith-rewriter") << "building real inequality from " << sum << std::endl;
  normalizeLCoeffAbsOne(sum);
  Node rhs = mkConst(nm, -removeConstant(sum));
  return buildRelation(k, collectSum(nm, sum), rhs);
}

std::pair<Node, Node> decomposeSum(NodeManager* nm,
                                   Sum&& sum,
                                   bool& negated,
                                   bool followLCoeffSign)
{
  negated = normalizeGCDLCM(sum, followLCoeffSign);
  RealAlgebraicNumber constant = removeConstant(sum);
  Assert(constant.isRational());
  Node c = nm->mkConstReal(constant.toRational());
  Node t = collectSum(nm, sum);
  return std::pair<Node, Node>(t, c);
}

std::pair<Node, Node> decomposeSum(NodeManager* nm, Sum&& sum)
{
  bool negated = false;
  return decomposeSum(nm, std::move(sum), negated, false);
}

std::pair<Node, Node> decomposeRelation(NodeManager* nm,
                                        const Node& a,
                                        const Node& b)
{
  Node ar = a.getKind() == Kind::TO_REAL ? a[0] : a;
  Node br = b.getKind() == Kind::TO_REAL ? b[0] : b;
  rewriter::Sum sum;
  rewriter::addToSum(sum, ar, false);
  rewriter::addToSum(sum, br, true);
  // decompose the sum into a non-constant and constant part
  normalizeGCDLCM(sum);
  RealAlgebraicNumber constant = removeConstant(sum);
  Assert(constant.isRational());
  // negate the constant
  Node c = nm->mkConstReal(-constant.toRational());
  Node t = collectSum(nm, sum);
  return std::pair<Node, Node>(t, c);
}

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
