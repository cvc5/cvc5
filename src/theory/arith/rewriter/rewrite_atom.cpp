/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

namespace {

/**
 * Build an integer equality from the given sum. The result is equivalent to the
 * sum being equal to zero. We first normalize the non-constant coefficients to
 * integers (using GCD and LCM). If the coefficient is non-integral after that,
 * the result is false. We then put the term with minimal absolute coefficient
 * to the left side of the equality and make its coefficient positive.
 * The sum is taken as rvalue as it is modified in the process.
 *
 * If isReal is true, the sides of the returned equality are cast to real
 * (via TO_REAL). This is used when the equality we are normalizing is an
 * equality between real terms, since the normal form of an equality must have
 * the same type as the equality we are normalizing.
 *
 * If negated is non-null, it is set to true if the difference of the sides of
 * the returned equality is a *negative* multiple of the given sum, and false
 * if it is a positive one.
 */
Node buildIntegerEquality(NodeManager* nm,
                          Sum&& sum,
                          bool isReal,
                          bool* negated)
{
  Trace("arith-rewriter") << "building integer equality from " << sum
                          << std::endl;
  if (sum.empty())
  {
    // The difference of the sides of the equality is zero, hence it is true.
    // Note this is possible if the sides of the equality are not in rewritten
    // form, e.g. for (= (+ x y) (+ y x)).
    return mkConst(nm, true);
  }
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
  if (negated != nullptr)
  {
    // If the coefficient of the removed monomial is negative, the equality we
    // build below is (-c*m = R) for the sum c*m + R, whose difference is the
    // negation of the sum. Otherwise it is (c*m = -R), whose difference is the
    // sum itself.
    *negated = (minabscoeff.second.sgn() < 0);
  }
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
  if (isReal)
  {
    // Use lhsr and rhsr to ensure deterministic node ID assignments
    Node lhsr = ensureReal(left);
    Node rhsr = ensureReal(rhs);
    // The equality we are rewriting was between real terms. We must not
    // change the type of the equality, hence we cast both sides back to real.
    return buildRelation(Kind::EQUAL, lhsr, rhsr);
  }
  return buildRelation(Kind::EQUAL, left, rhs);
}

/**
 * Build a real equality from the given sum. The result is equivalent to the sum
 * being equal to zero. We first extract the leading term and normalize its
 * coefficient to be plus or minus one. The result is the (normalized) leading
 * term being equal to the rest of the sum.
 * The sum is taken as rvalue as it is modified in the process.
 *
 * If negated is non-null, it is set to true if the difference of the sides of
 * the returned equality is a *negative* multiple of the given sum, and false
 * if it is a positive one.
 */
Node buildRealEquality(NodeManager* nm, Sum&& sum, bool* negated)
{
  Trace("arith-rewriter") << "building real equality from " << sum << std::endl;
  auto lterm = removeLTerm(nm, sum);
  if (negated != nullptr)
  {
    // If the coefficient c of the leading term t is negative, the difference of
    // the equality we build below is the sum scaled by 1/c, hence negative.
    // Note the coefficient is never zero here: it is zero only if the sum has
    // no leading term, i.e. it is empty or contains only a constant, in which
    // case it is integral and thus normalizeEquality used buildIntegerEquality
    // instead. This matters since marking both orientations of an equality as
    // negated would make the rewriter non-terminating.
    Assert(!lterm.second.isZero());
    *negated = (lterm.second.sgn() < 0);
  }
  if (lterm.second.isZero())
  {
    // Use zero to ensure deterministic node ID assignments
    Node zero = mkConst(nm, Integer(0));
    return buildRelation(Kind::EQUAL, zero, collectSum(nm, sum));
  }
  RealAlgebraicNumber lcoeff = -lterm.second;
  for (auto& s : sum)
  {
    s.second = s.second / lcoeff;
  }
  // Ensure real for both sides.
  Node lhs = lterm.first;
  Node rhs = collectSum(nm, sum);
  Node lhsr = ensureReal(lhs);
  Node rhsr = ensureReal(rhs);
  // Note that even if both sides are integer, we keep the equality between
  // real terms here, since the rewritten form of an equality must have the
  // same type as the equality we are rewriting.
  Assert(lhsr.getType().isReal() || lhsr.getType().isFullyAbstract());
  Assert(rhsr.getType().isReal() || rhsr.getType().isFullyAbstract());
  return buildRelation(Kind::EQUAL, lhsr, rhsr);
}

}  // namespace

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
  // Use rhsNode to ensure deterministic node ID assignments
  Node rhsNode = nm->mkConstInt(rhs);
  return buildRelation(Kind::GEQ, collectSum(nm, sum), rhsNode, negate);
}

Node buildRealInequality(NodeManager* nm, Sum&& sum, Kind k)
{
  Trace("arith-rewriter") << "building real inequality from " << sum
                          << std::endl;
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

Node normalizeEquality(NodeManager* nm, TNode atom, bool* negated)
{
  Assert(atom.getKind() == Kind::EQUAL);
  Assert(atom[0].getType().isRealOrInt());
  if (negated != nullptr)
  {
    *negated = false;
  }
  Node left = removeToReal(atom[0]);
  Node right = removeToReal(atom[1]);
  if (auto response = tryEvaluateRelationReflexive(Kind::EQUAL, left, right);
      response)
  {
    return mkConst(nm, *response);
  }
  if (auto response = tryEvaluateRelation(Kind::EQUAL, left, right); response)
  {
    return mkConst(nm, *response);
  }
  Sum sum;
  addToSum(sum, left, false);
  addToSum(sum, right, true);
  if (isIntegral(sum))
  {
    // Note that we may be normalizing an equality between real terms, e.g.
    // (= (to_real x) 1.0) for integer x. In this case, we ensure the
    // normalized form is an equality between real terms as well, since the
    // normalized form of an equality must have the same type.
    bool isReal = atom[0].getType().isReal();
    return buildIntegerEquality(nm, std::move(sum), isReal, negated);
  }
  return buildRealEquality(nm, std::move(sum), negated);
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
