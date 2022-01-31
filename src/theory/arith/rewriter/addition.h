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

#include <map>
#include <iosfwd>

#include "base/check.h"
#include "expr/node.h"
#include "theory/arith/rewriter/node_utils.h"
#include "theory/arith/rewriter/ordering.h"
#include "util/real_algebraic_number.h"

namespace cvc5::theory::arith::rewriter {

using Sum = std::map<Node, RealAlgebraicNumber, TermComparator>;

std::ostream& operator<<(std::ostream& os, const Sum& sum);


void addToSum(Sum& sum, TNode n, bool negate = false);

inline Node mkMultTerm(const Rational& multiplicity, TNode monomial)
{
  if (monomial.isConst())
  {
    return mkConst(multiplicity * monomial.getConst<Rational>());
  }
  if (isOne(multiplicity))
  {
    return monomial;
  }
  return NodeManager::currentNM()->mkNode(Kind::MULT, mkConst(multiplicity), monomial);
}

inline Node mkMultTerm(const RealAlgebraicNumber& multiplicity, TNode monomial)
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
  prod.insert(prod.end(), monomial.begin(), monomial.end());
  return mkNonlinearMult(prod);
}

/**
 * Turn a distributed sum (mapping of monomials to multiplicities) into a sum,
 * given as list of terms suitable to be passed to mkSum().
 */
Node collectSum(const Sum& sum);

Node collectSum(const Sum& sum,
                const RealAlgebraicNumber& basemultiplicity,
                const std::vector<Node>& baseproduct);

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
Node distributeMultiplication(const std::vector<TNode>& factors);

}  // namespace cvc5::theory::arith::rewriter

#endif
