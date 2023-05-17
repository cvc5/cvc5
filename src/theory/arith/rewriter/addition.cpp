/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Addition utilities for the arithmetic rewriter.
 */

#include "theory/arith/rewriter/addition.h"

#include <iostream>

#include "base/check.h"
#include "expr/node.h"
#include "theory/arith/rewriter/node_utils.h"
#include "theory/arith/rewriter/ordering.h"
#include "util/real_algebraic_number.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace rewriter {

std::ostream& operator<<(std::ostream& os, const Sum& sum)
{
  for (auto it = sum.begin(); it != sum.end(); ++it)
  {
    if (it != sum.begin()) os << " + ";
    if (it->first.isConst())
    {
      Assert(it->first.getConst<Rational>().isOne());
      os << it->second;
      continue;
    }
    os << it->second << "*" << it->first;
  }
  return os;
}

namespace
{

/**
 * Adds a factor n to a product, consisting of the numerical multiplicity and
 * the remaining (non-numerical) factors. If n is a product itself, its children
 * are merged into the product. If n is a constant or a real algebraic number,
 * it is multiplied to the multiplicity. Otherwise, n is added to product.
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
    case Kind::REAL_ALGEBRAIC_NUMBER: multiplicity *= getRAN(n); break;
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
 * Add a new summand, consisting of the product and the multiplicity, to a sum.
 * Either adds the summand as a new entry to the sum, or adds the multiplicity
 * to an already existing summand. Removes the entry, if the multiplicity is
 * zero afterwards.
 *
 * Invariant:
 *   add(s.n * s.ran for s in sum')
 *   = add(s.n * s.ran for s in sum) + multiplicity * product
 */
void addToSum(Sum& sum, TNode product, const RealAlgebraicNumber& multiplicity)
{
  if (multiplicity.isZero()) return;
  auto it = sum.find(product);
  if (it == sum.end())
  {
    sum.emplace(product, multiplicity);
  }
  else
  {
    it->second += multiplicity;
    if (it->second.isZero())
    {
      sum.erase(it);
    }
  }
}

/**
 * Evaluates `basemultiplicity * baseproduct * sum` into a single node (of kind
 * `ADD`, unless the sum has less than two summands).
 */
Node collectSumWithBase(const Sum& sum,
                        const RealAlgebraicNumber& basemultiplicity,
                        const std::vector<Node>& baseproduct)
{
  if (sum.empty()) return mkConst(Rational(0));
  // construct the sum as nodes.
  NodeBuilder nb(Kind::ADD);
  for (const auto& summand : sum)
  {
    Assert(!summand.second.isZero());
    RealAlgebraicNumber mult = summand.second * basemultiplicity;
    std::vector<Node> product = baseproduct;
    rewriter::addToProduct(product, mult, summand.first);
    nb << mkMultTerm(mult, std::move(product));
  }
  if (nb.getNumChildren() == 1)
  {
    return nb[0];
  }
  return nb.constructNode();
}
}

bool isIntegral(const Sum& sum)
{
  std::vector<TNode> queue;
  for (const auto& s: sum)
  {
    queue.emplace_back(s.first);
  }
  while (!queue.empty())
  {
    TNode cur = queue.back();
    queue.pop_back();

    if (cur.isConst()) continue;
    switch (cur.getKind())
    {
      case Kind::ADD:
      case Kind::NEG:
      case Kind::SUB:
      case Kind::MULT:
      case Kind::NONLINEAR_MULT:
        queue.insert(queue.end(), cur.begin(), cur.end());
        break;
      default:
        if (!cur.getType().isInteger()) return false;
    }
  }
  return true;
}

void addToSum(Sum& sum, TNode n, bool negate)
{
  if (n.getKind() == Kind::ADD)
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
  addToSum(sum, mkNonlinearMult(monomial), multiplicity);
}

Node collectSum(const Sum& sum)
{
  if (sum.empty()) return mkConst(Rational(0));
  Trace("arith-rewriter") << "Collecting sum " << sum << std::endl;
  // construct the sum as nodes.
  NodeBuilder nb(Kind::ADD);
  for (const auto& s : sum)
  {
    nb << mkMultTerm(s.second, s.first);
  }
  if (nb.getNumChildren() == 1)
  {
    return nb[0];
  }
  return nb.constructNode();
}

Node distributeMultiplication(const std::vector<TNode>& factors)
{
  if (TraceIsOn("arith-rewriter-distribute"))
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
  Sum sum;
  // Add a base summand
  sum.emplace(mkConst(Rational(1)), RealAlgebraicNumber(Integer(1)));

  // multiply factors one by one to basmultiplicity * base * sum
  for (const auto& factor : factors)
  {
    // Subtractions are rewritten already, we only need to care about additions
    Assert(factor.getKind() != Kind::SUB);
    Assert(factor.getKind() != Kind::NEG
           || (factor[0].isConst() || isRAN(factor[0])));
    if (factor.getKind() != Kind::ADD)
    {
      Assert(!(factor.isConst() && factor.getConst<Rational>().isZero()));
      addToProduct(base, basemultiplicity, factor);
      continue;
    }
    // temporary to store factor * sum, will be moved to sum at the end
    Sum newsum;

    for (const auto& summand : sum)
    {
      for (const auto& child : factor)
      {
        // add summand * child to newsum
        RealAlgebraicNumber multiplicity = summand.second;
        if (child.isConst())
        {
          multiplicity *= child.getConst<Rational>();
          addToSum(newsum, summand.first, multiplicity);
          continue;
        }
        if (isRAN(child))
        {
          multiplicity *= getRAN(child);
          addToSum(newsum, summand.first, multiplicity);
          continue;
        }

        // construct the new product
        std::vector<Node> newProduct;
        addToProduct(newProduct, multiplicity, summand.first);
        addToProduct(newProduct, multiplicity, child);
        std::sort(newProduct.begin(), newProduct.end(), LeafNodeComparator());
        addToSum(newsum, mkNonlinearMult(newProduct), multiplicity);
      }
    }
    if (TraceIsOn("arith-rewriter-distribute"))
    {
      Trace("arith-rewriter-distribute")
          << "multiplied with " << factor << std::endl;
      Trace("arith-rewriter-distribute")
          << "base: " << basemultiplicity << " * " << base << std::endl;
      Trace("arith-rewriter-distribute") << "sum:" << std::endl;
      for (const auto& summand : newsum)
      {
        Trace("arith-rewriter-distribute")
            << "\t" << summand.second << " * " << summand.first << std::endl;
      }
    }

    sum = std::move(newsum);
  }
  // now mult(factors) == base * add(sum)

  return collectSumWithBase(sum, basemultiplicity, base);
}

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
