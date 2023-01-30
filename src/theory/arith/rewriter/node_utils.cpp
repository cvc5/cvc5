/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for nodes in the arithmetic rewriter.
 */

#include "theory/arith/rewriter/node_utils.h"

#include "base/check.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/rewriter/ordering.h"

namespace cvc5::internal {
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
  Node mterm = mkConst(multiplicity);
  if (mterm.isConst())
  {
    return mkMultTerm(mterm.getConst<Rational>(), monomial);
  }
  if (monomial.isConst())
  {
    return mkConst(multiplicity * monomial.getConst<Rational>());
  }
  std::vector<Node> prod;
  prod.emplace_back(mterm);
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
  Node mterm = mkConst(multiplicity);
  if (mterm.isConst())
  {
    std::sort(monomial.begin(), monomial.end(), rewriter::LeafNodeComparator());
    return mkMultTerm(mterm.getConst<Rational>(), mkNonlinearMult(monomial));
  }
  monomial.emplace_back(mterm);
  std::sort(monomial.begin(), monomial.end(), rewriter::LeafNodeComparator());
  Assert(monomial.size() >= 2);
  return NodeManager::currentNM()->mkNode(Kind::NONLINEAR_MULT, monomial);
}

TNode removeToReal(TNode t) { return t.getKind() == kind::TO_REAL ? t[0] : t; }

Node maybeEnsureReal(TypeNode tn, TNode t)
{
  // if we require being a real
  if (!tn.isInteger())
  {
    // ensure that t has type real
    Assert(tn.isReal());
    return ensureReal(t);
  }
  return t;
}

Node ensureReal(TNode t)
{
  if (t.getType().isInteger())
  {
    if (t.isConst())
    {
      // short-circuit
      Node ret = NodeManager::currentNM()->mkConstReal(t.getConst<Rational>());
      Assert(ret.getType().isReal());
      return ret;
    }
    Trace("arith-rewriter-debug") << "maybeEnsureReal: " << t << std::endl;
    return NodeManager::currentNM()->mkNode(kind::TO_REAL, t);
  }
  return t;
}

Node getFactors(const Node& n, std::vector<Node>& factors)
{
  Kind nk = n.getKind();
  if (nk == kind::CONST_INTEGER)
  {
    return n;
  }
  else if (nk == kind::NONLINEAR_MULT)
  {
    factors.insert(factors.end(), n.begin(), n.end());
    std::sort(factors.begin(), factors.end());
  }
  else if (nk == kind::MULT)
  {
    Assert(n[0].isConst());
    factors.push_back(n[1]);
    return n[0];
  }
  else
  {
    factors.push_back(n);
  }
  return Node::null();
}

bool simpleNonzeroFactoring(Node& num, Node& den)
{
  if (den.getKind() == kind::ADD)
  {
    return false;
  }
  Trace("simple-factor") << "Simple factor " << num << " / " << den
                         << std::endl;
  std::vector<Node> nfactors;
  Node cden = getFactors(den, nfactors);
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSum(num, msum))
  {
    Trace("simple-factor") << "...failed to get sum" << std::endl;
    return false;
  }
  Assert (cden.isConst() && cden.getType().isInteger());
  Integer di = cden.getConst<Rational>().getNumerator().abs();
  Trace("simple-factor") << "Factors denominator: " << cden << ", " << nfactors
                         << std::endl;
  // compute what factors are not divisible
  std::vector<Node> factors = nfactors;
  for (const std::pair<const Node, Node>& m : msum)
  {
    Trace("simple-factor") << "Factor " << m.first << " -> " << m.second
                           << std::endl;
    // process the constant factor using gcd
    if (!di.isOne())
    {
      if (!m.second.isNull())
      {
        Assert (m.second.isConst() && m.second.getType().isInteger());
        di = di.gcd(m.second.getConst<Rational>().getNumerator().abs());
      }
      else
      {
        di = Integer(1);
      }
      Trace("simple-factor") << "  Constant gcd now: " << di << std::endl;
    }
    // process the non-constant factor using set intersection
    std::vector<Node> newFactors;
    if (!factors.empty())
    {
      if (!m.first.isNull())
      {
        std::vector<Node> mfactors;
        getFactors(m.first, mfactors);
        Trace("simple-factor") << "  Monomial factors are: " << mfactors
                              << std::endl;
        std::set_intersection(factors.begin(),
                              factors.end(),
                              mfactors.begin(),
                              mfactors.end(),
                              std::back_inserter(newFactors));
      }
      Trace("simple-factor") << "  Factors now: " << newFactors << std::endl;
    }
    // if both components trivial, we are done
    if (newFactors.empty() && di.isOne())
    {
      Trace("simple-factor") << "...no factoring" << std::endl;
      return false;
    }
    factors = newFactors;
  }
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> newChildren;
  for (const std::pair<const Node, Node>& m : msum)
  {
    std::vector<Node> mfactors;
    getFactors(m.first, mfactors);
    std::vector<Node> mfactorsFinal;
    std::set_difference(mfactors.begin(),
                        mfactors.end(),
                        factors.begin(),
                        factors.end(),
                        std::back_inserter(mfactorsFinal));
    if (!m.second.isNull())
    {
      Node mcFinal = m.second;
      if (!di.isOne())
      {
        mcFinal = nm->mkConstInt(mcFinal.getConst<Rational>()/Rational(di));
      }
      mfactorsFinal.push_back(mcFinal);
    }
    newChildren.push_back(mkNonlinearMult(mfactorsFinal));
  }
  Assert(!newChildren.empty());
  num = newChildren.size() == 1 ? newChildren[0]
                                : nm->mkNode(kind::ADD, newChildren);
  std::vector<Node> nfactorsFinal;
  std::set_difference(nfactors.begin(),
                      nfactors.end(),
                      factors.begin(),
                      factors.end(),
                      std::back_inserter(nfactorsFinal));
  if (!cden.isNull())
  {
    Node cdenFinal = cden;
    if (!di.isOne())
    {
      cdenFinal = nm->mkConstInt(cden.getConst<Rational>()/Rational(di));
    }
    nfactorsFinal.push_back(cdenFinal);
  }
  den = mkNonlinearMult(nfactorsFinal);
  Trace("simple-factor") << "...return " << num << " / " << den << std::endl;
  return true;
}

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
