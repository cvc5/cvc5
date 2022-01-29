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
 * Addition utilities for the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__ADDITION_H
#define CVC5__THEORY__ARITH__REWRITER__ADDITION_H

#include <unordered_map>

#include "base/check.h"
#include "expr/node.h"
#include "theory/arith/rewriter/node_utils.h"
#include "theory/arith/rewriter/ordering.h"
#include "util/real_algebraic_number.h"

namespace cvc5::theory::arith::rewriter {

using Sum = std::unordered_map<Node, RealAlgebraicNumber>;
using Summands = std::vector<std::pair<Node, RealAlgebraicNumber>>;

/**
 * Adds a factor n to a product, consisting of the numerical multiplicity and
 * the remaining (non-numerical) factors. If n is a product itself, its children
 * are merged into a product. If n is a constant or a real algebraic number, it
 * is multiplied to the multiplicity. Otherwise, n is added to product.
 *
 * Invariant:
 *   multiplicity' * multiply(product') = n * multiplicity * multiply(product)
 */
void addToProduct(std::vector<Node>& product,
                  RealAlgebraicNumber& multiplicity,
                  TNode n)
{
  switch (n.getKind())
  {
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
      for (const auto& child : n)
      {
        // make sure constants are properly extracted.
        // recursion is safe, as mult is already flattened
        addToProduct(product, multiplicity, child);
      }
      break;
    case Kind::REAL_ALGEBRAIC_NUMBER:
      multiplicity *= n.getOperator().getConst<RealAlgebraicNumber>();
      break;
    default:
      if (n.isConst())
      {
        multiplicity *= n.getConst<Rational>();
      }
      else
      {
        product.emplace_back(n);
      }
  }
}

/**
 * Add a new summand, consisting of the product and the multiplicity, to a sum
 * as used in the distribution of multiplication. Either adds the summand as a
 * new entry to sum, or adds the multiplicity to an already existing summand.
 *
 * Invariant:
 *   add(s.n * s.ran for s in sum')
 *   = add(s.n * s.ran for s in sum) + multiplicity * product
 */
void addToSum(Sum& sum, TNode product, const RealAlgebraicNumber& multiplicity)
{
  if (isZero(multiplicity)) return;
  auto it = sum.find(product);
  if (it == sum.end())
  {
    sum.emplace(product, multiplicity);
  }
  else
  {
    it->second += multiplicity;
    if (isZero(it->second))
    {
      sum.erase(it);
    }
  }
}

void addToSum(Sum& sum, TNode n, bool negate = false)
{
  if (n.getKind() == Kind::PLUS)
  {
    for (const auto& child : n)
    {
      addToSum(sum, child, negate);
    }
    return;
  }
  std::vector<Node> monomial;
  RealAlgebraicNumber multiplicity(Integer(1));
  if (negate)
  {
    multiplicity = Integer(-1);
  }
  addToProduct(monomial, multiplicity, n);
  addToSum(sum, mkMult(std::move(monomial)), multiplicity);
}

Node mkMultTerm(const RealAlgebraicNumber& multiplicity, TNode monomial)
{
  auto* nm = NodeManager::currentNM();
  if (monomial.isConst())
  {
    return mkConst(multiplicity * monomial.getConst<Rational>());
  }
  if (multiplicity.isRational())
  {
    if (isOne(multiplicity))
    {
      return monomial;
    }
    return nm->mkNode(Kind::MULT, mkConst(multiplicity.toRational()), monomial);
  }
  std::vector<Node> prod;
  prod.emplace_back(mkConst(multiplicity));
  prod.insert(prod.end(), monomial.begin(), monomial.end());
  return mkMult(std::move(prod));
}

Node mkMultTerm(const Rational& multiplicity, TNode monomial)
{
  auto* nm = NodeManager::currentNM();
  if (monomial.isConst())
  {
    return mkConst(multiplicity * monomial.getConst<Rational>());
  }
  if (isOne(multiplicity))
  {
    return monomial;
  }
  return nm->mkNode(Kind::MULT, mkConst(multiplicity), monomial);
}

namespace normalize {

void LCoeffAbsOne(Summands& sum)
{
  if (sum.empty()) return;
  if (sum.size() == 1)
  {
    // Trivial if there is only one summand
    sum.front().second = Integer(sgn(sum.front().second) > 0 ? 1 : -1);
    return;
  }
  // LCoeff is first coefficient of non-constant monomial
  RealAlgebraicNumber lcoeff;
  if (sum.front().first.isConst())
  {
    lcoeff = sum[1].second;
  }
  else
  {
    lcoeff = sum.front().second;
  }
  if (sgn(lcoeff) < 0)
  {
    lcoeff = -lcoeff;
  }
  if (isOne(lcoeff)) return;
  for (auto& s : sum)
  {
    s.second = s.second / lcoeff;
  }
}

bool GCDLCM(Summands& sum, bool followLCoeffSign = false)
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
    size_t id = sum.front().first.isConst() ? 1 : 0;
    if (sgn(sum[id].second) < 0)
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
}  // namespace normalize

RealAlgebraicNumber removeConstant(Summands& summands)
{
  RealAlgebraicNumber res;
  if (!summands.empty() && summands.front().first.isConst())
  {
    Assert(summands.front().first.getConst<Rational>().isOne());
    res = summands.front().second;
    summands.erase(summands.begin());
  }
  return res;
}

std::pair<Node, RealAlgebraicNumber> removeMinAbsCoeff(Summands& summands)
{
  auto minit = summands.begin();
  while (minit != summands.end() && minit->first.isConst()) ++minit;
  for (auto it = minit; it != summands.end(); ++it)
  {
    if (it->first.isConst()) continue;
    if (it->second.toRational().absCmp(minit->second.toRational()) < 0)
    {
      minit = it;
    }
  }
  if (minit == summands.end())
  {
    return std::make_pair(mkConst(Integer(1)), Integer(0));
  }
  Assert(minit != summands.end());
  std::pair<Node, RealAlgebraicNumber> res = *minit;
  summands.erase(minit);
  return res;
}

std::pair<Node, RealAlgebraicNumber>& getLTerm(Summands& summands)
{
  auto it = summands.begin();
  while (it != summands.end() && it->first.isConst()) ++it;
  Assert(it != summands.end());
  return *it;
}

std::pair<Node, RealAlgebraicNumber> removeLTerm(Summands& summands)
{
  auto it = summands.begin();
  while (it != summands.end() && it->first.isConst()) ++it;
  if (it == summands.end())
  {
    return std::make_pair(mkConst(Integer(1)), Integer(0));
  }
  Assert(it != summands.end());
  std::pair<Node, RealAlgebraicNumber> res = *it;
  summands.erase(it);
  return res;
}

Summands gatherSummands(const Sum& sum)
{
  Summands summands;
  for (const auto& summand : sum)
  {
    Assert(!isZero(summand.second));
    summands.emplace_back(summand.first, summand.second);
  }
  std::sort(summands.begin(), summands.end(), [](const auto& a, const auto& b) {
    return ProductNodeComparator()(a.first, b.first);
  });
  return summands;
}

/**
 * Turn a distributed sum (mapping of monomials to multiplicities) into a sum,
 * given as list of terms suitable to be passed to mkSum().
 */
Node collectSum(const Sum& sum)
{
  if (sum.empty()) return mkConst(Rational(0));
  // construct the sum as nodes.
  std::vector<std::pair<Node, RealAlgebraicNumber>> summands =
      gatherSummands(sum);
  std::vector<Node> children;
  for (const auto& s : summands)
  {
    children.emplace_back(mkMultTerm(s.second, s.first));
  }
  return mkSum(std::move(children));
}

Node collectSum(const Sum& sum,
                const RealAlgebraicNumber& basemultiplicity,
                const std::vector<Node>& baseproduct)
{
  if (sum.empty()) return mkConst(Rational(0));
  // construct the sum as nodes.
  Summands summands;
  for (const auto& summand : sum)
  {
    Assert(!isZero(summand.second));
    RealAlgebraicNumber mult = summand.second * basemultiplicity;
    std::vector<Node> product = baseproduct;
    rewriter::addToProduct(product, mult, summand.first);
    std::sort(product.begin(), product.end(), rewriter::LeafNodeComparator());
    summands.emplace_back(mkMult(std::move(product)), mult);
  }
  std::sort(summands.begin(), summands.end(), [](const auto& a, const auto& b) {
    return ProductNodeComparator()(a.first, b.first);
  });
  std::vector<Node> children;
  for (const auto& s : summands)
  {
    children.emplace_back(mkMultTerm(s.second, s.first));
  }
  return mkSum(std::move(children));
}

Node collectSum(const Summands& summands)
{
  std::vector<Node> children;
  for (const auto& s : summands)
  {
    children.emplace_back(mkMultTerm(s.second, s.first));
  }
  return mkSum(std::move(children));
}

/**
 * Distribute a multiplication over one or more additions. The multiplication
 * is given as the list of its factors. Though this method also works if none
 * of these factors is an addition, there is no point of calling this method
 * in this case. The result is the resulting sum after expanding the product
 * and pushing the multiplication inside the addition.
 *
 * The method maintains a `sum` as a mapping from Node to RealAlgebraicNumber.
 * The nodes can be understood as monomials, or generally non-value parts of
 * the product, while the real algebraic numbers are the multiplicities of these
 * monomials or products. This allows to combine summands with identical
 * monomials immediately and avoid a potential blow-up.
 */
Node distributeMultiplication(const std::vector<TNode>& factors)
{
  if (Trace.isOn("arith-rewriter-distribute"))
  {
    Trace("arith-rewriter-distribute") << "Distributing" << std::endl;
    for (const auto& f : factors)
    {
      Trace("arith-rewriter-distribute") << "\t" << f << std::endl;
    }
  }
  // factors that are not sums, separated into numerical and non-numerical
  RealAlgebraicNumber basemultiplicity(Integer(1));
  std::vector<Node> base;
  // maps products to their (possibly real algebraic) multiplicities.
  // The current (intermediate) value is the sum of these (multiplied by the
  // base factors).
  Sum rsum;
  // Add a base summand
  rsum.emplace(mkConst(Rational(1)), RealAlgebraicNumber(Integer(1)));

  // multiply factors one by one to basmultiplicity * base * sum
  for (const auto& factor : factors)
  {
    // Subtractions are rewritten already, we only need to care about additions
    Assert(factor.getKind() != Kind::MINUS);
    Assert(factor.getKind() != Kind::UMINUS
           || (factor[0].isConst() || isRAN(factor[0])));
    if (factor.getKind() != Kind::PLUS)
    {
      Assert(!(factor.isConst() && factor.getConst<Rational>().isZero()));
      addToProduct(base, basemultiplicity, factor);
      continue;
    }
    // temporary to store factor * sum, will be moved to sum at the end
    Sum newrsum;

    for (const auto& summand : rsum)
    {
      for (const auto& child : factor)
      {
        // add summand * child to newsum
        RealAlgebraicNumber multiplicity = summand.second;
        if (child.isConst())
        {
          multiplicity *= child.getConst<Rational>();
          addToSum(newrsum, summand.first, multiplicity);
          continue;
        }
        if (isRAN(child))
        {
          multiplicity *= getRAN(child);
          addToSum(newrsum, summand.first, multiplicity);
          continue;
        }

        // construct the new product
        std::vector<Node> newProduct;
        addToProduct(newProduct, multiplicity, summand.first);
        addToProduct(newProduct, multiplicity, child);
        std::sort(newProduct.begin(), newProduct.end(), LeafNodeComparator());
        addToSum(newrsum, mkMult(std::move(newProduct)), multiplicity);
      }
    }
    Trace("arith-rewriter-distribute")
        << "multiplied with " << factor << std::endl;
    Trace("arith-rewriter-distribute")
        << "base: " << basemultiplicity << " * " << base << std::endl;
    Trace("arith-rewriter-distribute") << "sum:" << std::endl;
    for (const auto& summand : newrsum)
    {
      Trace("arith-rewriter-distribute")
          << "\t" << summand.second << " * " << summand.first << std::endl;
    }

    rsum = std::move(newrsum);
  }
  // now mult(factors) == base * add(sum)

  return collectSum(rsum, basemultiplicity, base);
}

}  // namespace cvc5::theory::arith::rewriter

#endif
