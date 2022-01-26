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

struct Sum
{
    std::unordered_map<Node, RealAlgebraicNumber> sum;
};

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
void addToSum(Sum& sum,
                  TNode product,
                  const RealAlgebraicNumber& multiplicity)
{
  if (isZero(multiplicity)) return;
  auto it = sum.sum.find(product);
  if (it == sum.sum.end())
  {
    sum.sum.emplace(product, multiplicity);
  }
  else
  {
    it->second += multiplicity;
    if (isZero(it->second))
    {
      sum.sum.erase(it);
    }
  }
}

void addToSum(Sum& sum, TNode n, bool negate = false)
{
  if (n.getKind() == Kind::PLUS)
  {
    for (const auto& child: n)
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
  if (multiplicity.isRational())
  {
    if (isOne(multiplicity))
    {
      return monomial;
    }
    if (monomial.isConst())
    {
      return nm->mkConstReal(multiplicity.toRational() * monomial.getConst<Rational>());
    }
    return nm->mkNode(Kind::MULT, nm->mkConstReal(multiplicity.toRational()), monomial);
  }
  if (monomial.isConst())
  {
    return nm->mkRealAlgebraicNumber(multiplicity * monomial.getConst<Rational>());
  }
  std::vector<Node> prod;
  prod.emplace_back(nm->mkRealAlgebraicNumber(multiplicity));
  prod.insert(prod.end(), monomial.begin(), monomial.end());
  return mkMult(std::move(prod));
}

/**
 * Turn a distributed sum (mapping of monomials to multiplicities) into a sum,
 * given as list of terms suitable to be passed to mkSum().
 */
std::vector<Node> collectSum(
    const Sum& sum)
{
  if (sum.sum.empty()) return {};
  // construct the sum as nodes.
  std::vector<std::pair<Node, RealAlgebraicNumber>> summands;
  for (const auto& summand : sum.sum)
  {
    Assert(!isZero(summand.second));
    summands.emplace_back(summand.first, summand.second);
  }
  std::sort(summands.begin(), summands.end(), [](const auto& a, const auto& b) {
    return ProductNodeComparator()(a.first, b.first);
  });
  std::vector<Node> children;
  for (const auto& s : summands)
  {
    children.emplace_back(mkMultTerm(s.second, s.first));
  }
  return children;
}

}

#endif
