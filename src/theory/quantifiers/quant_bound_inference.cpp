/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifiers bound inference.
 */

#include "theory/quantifiers/quant_bound_inference.h"

#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

QuantifiersBoundInference::QuantifiersBoundInference(unsigned cardMax,
                                                     bool isFmf)
    : d_cardMax(cardMax), d_isFmf(isFmf), d_bint(nullptr)
{
}

void QuantifiersBoundInference::finishInit(BoundedIntegers* b) { d_bint = b; }

bool QuantifiersBoundInference::mayComplete(TypeNode tn)
{
  std::unordered_map<TypeNode, bool>::iterator it = d_may_complete.find(tn);
  if (it == d_may_complete.end())
  {
    // cache
    bool mc = mayComplete(tn, d_cardMax);
    d_may_complete[tn] = mc;
    return mc;
  }
  return it->second;
}

bool QuantifiersBoundInference::mayComplete(TypeNode tn, unsigned maxCard)
{
  if (!tn.isClosedEnumerable())
  {
    return false;
  }
  bool mc = false;
  // we cannot use FMF to complete interpreted types, thus we pass
  // false for fmfEnabled here
  if (isCardinalityClassFinite(tn.getCardinalityClass(), false))
  {
    Cardinality c = tn.getCardinality();
    if (!c.isLargeFinite())
    {
      NodeManager* nm = NodeManager::currentNM();
      Node card = nm->mkConst(Rational(c.getFiniteCardinality()));
      // check if less than fixed upper bound
      Node oth = nm->mkConst(Rational(maxCard));
      Node eq = nm->mkNode(LEQ, card, oth);
      eq = Rewriter::rewrite(eq);
      mc = eq.isConst() && eq.getConst<bool>();
    }
  }
  return mc;
}

bool QuantifiersBoundInference::isFiniteBound(Node q, Node v)
{
  if (d_bint && d_bint->isBound(q, v))
  {
    return true;
  }
  TypeNode tn = v.getType();
  if (tn.isSort() && d_isFmf)
  {
    return true;
  }
  else if (mayComplete(tn))
  {
    return true;
  }
  return false;
}

BoundVarType QuantifiersBoundInference::getBoundVarType(Node q, Node v)
{
  if (d_bint)
  {
    return d_bint->getBoundVarType(q, v);
  }
  return isFiniteBound(q, v) ? BOUND_FINITE : BOUND_NONE;
}

void QuantifiersBoundInference::getBoundVarIndices(
    Node q, std::vector<unsigned>& indices) const
{
  Assert(indices.empty());
  // we take the bounded variables first
  if (d_bint)
  {
    d_bint->getBoundVarIndices(q, indices);
  }
  // then get the remaining ones
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    if (std::find(indices.begin(), indices.end(), i) == indices.end())
    {
      indices.push_back(i);
    }
  }
}

bool QuantifiersBoundInference::getBoundElements(
    RepSetIterator* rsi,
    bool initial,
    Node q,
    Node v,
    std::vector<Node>& elements) const
{
  if (d_bint)
  {
    return d_bint->getBoundElements(rsi, initial, q, v, elements);
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
