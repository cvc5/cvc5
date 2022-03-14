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
 * Utilities for nodes in the arithmetic rewriter.
 */

#include "theory/arith/rewriter/node_utils.h"

#include "base/check.h"
#include "theory/arith/rewriter/ordering.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace rewriter {

Node mkMultTerm(const Rational& multiplicity, TNode monomial)
{
  if (monomial.isConst())
  {
    return mkConst(multiplicity * monomial.getConst<Rational>());
  }
  if (isOne(multiplicity))
  {
    return monomial;
  }
  return NodeManager::currentNM()->mkNode(
      Kind::MULT, mkConst(multiplicity), monomial);
}

Node mkMultTerm(const RealAlgebraicNumber& multiplicity, TNode monomial)
{
  if (multiplicity.isRational())
  {
    return mkMultTerm(multiplicity.toRational(), monomial);
  }
  if (monomial.isConst())
  {
    return mkConst(multiplicity * monomial.getConst<Rational>());
  }
  std::vector<Node> prod;
  prod.emplace_back(mkConst(multiplicity));
  if (monomial.getKind() == Kind::MULT || monomial.getKind() == Kind::NONLINEAR_MULT)
  {
    prod.insert(prod.end(), monomial.begin(), monomial.end());
  }
  else
  {
    prod.emplace_back(monomial);
  }
  Assert(prod.size() >= 2);
  return NodeManager::currentNM()->mkNode(Kind::NONLINEAR_MULT, prod);
}

Node mkMultTerm(const RealAlgebraicNumber& multiplicity,
                std::vector<Node>&& monomial)
{
  if (monomial.empty())
  {
    return mkConst(multiplicity);
  }
  if (multiplicity.isRational())
  {
    std::sort(monomial.begin(), monomial.end(), rewriter::LeafNodeComparator());
    return mkMultTerm(multiplicity.toRational(), mkNonlinearMult(monomial));
  }
  monomial.emplace_back(mkConst(multiplicity));
  std::sort(monomial.begin(), monomial.end(), rewriter::LeafNodeComparator());
  Assert(monomial.size() >= 2);
  return NodeManager::currentNM()->mkNode(Kind::NONLINEAR_MULT, monomial);
}

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
