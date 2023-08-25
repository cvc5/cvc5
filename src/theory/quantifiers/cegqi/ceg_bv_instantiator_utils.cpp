/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ceg_bv_instantiator.
 */

#include "theory/quantifiers/cegqi/ceg_bv_instantiator_utils.h"

#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

BvInstantiatorUtil::BvInstantiatorUtil(Env& env) : EnvObj(env) {}

Node BvInstantiatorUtil::getPvCoeff(TNode pv, TNode n) const
{
  bool neg = false;
  Node coeff;

  if (n.getKind() == BITVECTOR_NEG)
  {
    neg = true;
    n = n[0];
  }

  if (n == pv)
  {
    coeff = bv::utils::mkOne(bv::utils::getSize(pv));
  }
  /* All multiplications are normalized to pv * (t1 * t2). */
  else if (n.getKind() == BITVECTOR_MULT && n.getAttribute(BvLinearAttribute()))
  {
    Assert(n.getNumChildren() == 2);
    Assert(n[0] == pv);
    coeff = n[1];
  }
  else /* n is in no form to extract the coefficient for pv */
  {
    Trace("cegqi-bv-nl") << "Cannot extract coefficient for " << pv << " in "
                         << n << std::endl;
    return Node::null();
  }
  Assert(!coeff.isNull());

  if (neg) return NodeManager::currentNM()->mkNode(BITVECTOR_NEG, coeff);
  return coeff;
}

Node BvInstantiatorUtil::normalizePvMult(
    TNode pv,
    const std::vector<Node>& children,
    std::unordered_map<Node, bool>& contains_pv) const
{
  bool neg, neg_coeff = false;
  bool found_pv = false;
  NodeManager* nm;
  NodeBuilder nb(BITVECTOR_MULT);
  BvLinearAttribute is_linear;

  nm = NodeManager::currentNM();
  for (TNode nc : children)
  {
    if (!contains_pv[nc])
    {
      nb << nc;
      continue;
    }

    neg = false;
    if (nc.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      nc = nc[0];
    }

    if (!found_pv && nc == pv)
    {
      found_pv = true;
      neg_coeff = neg;
      continue;
    }
    else if (!found_pv && nc.getKind() == BITVECTOR_MULT
             && nc.getAttribute(is_linear))
    {
      Assert(nc.getNumChildren() == 2);
      Assert(nc[0] == pv);
      Assert(!contains_pv[nc[1]]);
      found_pv = true;
      neg_coeff = neg;
      nb << nc[1];
      continue;
    }
    return Node::null(); /* non-linear */
  }
  Assert(nb.getNumChildren() > 0);

  Node coeff = (nb.getNumChildren() == 1) ? nb[0] : nb.constructNode();
  if (neg_coeff)
  {
    coeff = nm->mkNode(BITVECTOR_NEG, coeff);
  }
  coeff = rewrite(coeff);
  unsigned size_coeff = bv::utils::getSize(coeff);
  Node zero = bv::utils::mkZero(size_coeff);
  if (coeff == zero)
  {
    return zero;
  }
  Node result;
  if (found_pv)
  {
    if (coeff == bv::utils::mkOne(size_coeff))
    {
      return pv;
    }
    result = nm->mkNode(BITVECTOR_MULT, pv, coeff);
    contains_pv[result] = true;
    result.setAttribute(is_linear, true);
  }
  else
  {
    result = coeff;
  }
  return result;
}

bool BvInstantiatorUtil::isLinearPlus(
    TNode n, TNode pv, std::unordered_map<Node, bool>& contains_pv) const
{
  Node coeff;
  Assert(n.getAttribute(BvLinearAttribute()));
  Assert(n.getNumChildren() == 2);
  if (n[0] != pv)
  {
    Assert(n[0].getKind() == BITVECTOR_MULT);
    Assert(n[0].getNumChildren() == 2);
    Assert(n[0][0] == pv);
    Assert(!contains_pv[n[0][1]]);
  }
  Assert(!contains_pv[n[1]]);
  coeff = getPvCoeff(pv, n[0]);
  Assert(!coeff.isNull());
  Assert(!contains_pv[coeff]);
  return true;
}

Node BvInstantiatorUtil::normalizePvPlus(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<Node, bool>& contains_pv) const
{
  NodeManager* nm;
  NodeBuilder nb_c(BITVECTOR_ADD);
  NodeBuilder nb_l(BITVECTOR_ADD);
  BvLinearAttribute is_linear;
  bool neg;

  nm = NodeManager::currentNM();
  for (TNode nc : children)
  {
    if (!contains_pv[nc])
    {
      nb_l << nc;
      continue;
    }

    neg = false;
    if (nc.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      nc = nc[0];
    }

    if (nc == pv
        || (nc.getKind() == BITVECTOR_MULT && nc.getAttribute(is_linear)))
    {
      Node coeff = getPvCoeff(pv, nc);
      Assert(!coeff.isNull());
      if (neg)
      {
        coeff = nm->mkNode(BITVECTOR_NEG, coeff);
      }
      nb_c << coeff;
      continue;
    }
    else if (nc.getKind() == BITVECTOR_ADD && nc.getAttribute(is_linear))
    {
      Assert(isLinearPlus(nc, pv, contains_pv));
      Node coeff = getPvCoeff(pv, nc[0]);
      Assert(!coeff.isNull());
      Node leaf = nc[1];
      if (neg)
      {
        coeff = nm->mkNode(BITVECTOR_NEG, coeff);
        leaf = nm->mkNode(BITVECTOR_NEG, leaf);
      }
      nb_c << coeff;
      nb_l << leaf;
      continue;
    }
    /* can't collect coefficients of 'pv' in 'cur' -> non-linear */
    return Node::null();
  }
  Assert(nb_c.getNumChildren() > 0 || nb_l.getNumChildren() > 0);

  Node pv_mult_coeffs, result;
  if (nb_c.getNumChildren() > 0)
  {
    Node coeffs = (nb_c.getNumChildren() == 1) ? nb_c[0] : nb_c.constructNode();
    coeffs = rewrite(coeffs);
    result = pv_mult_coeffs = normalizePvMult(pv, {pv, coeffs}, contains_pv);
  }

  if (nb_l.getNumChildren() > 0)
  {
    Node leafs = (nb_l.getNumChildren() == 1) ? nb_l[0] : nb_l.constructNode();
    leafs = rewrite(leafs);
    Node zero = bv::utils::mkZero(bv::utils::getSize(pv));
    /* pv * 0 + t --> t */
    if (pv_mult_coeffs.isNull() || pv_mult_coeffs == zero)
    {
      result = leafs;
    }
    else
    {
      result = nm->mkNode(BITVECTOR_ADD, pv_mult_coeffs, leafs);
      contains_pv[result] = true;
      result.setAttribute(is_linear, true);
    }
  }
  Assert(!result.isNull());
  return result;
}

Node BvInstantiatorUtil::normalizePvEqual(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<Node, bool>& contains_pv) const
{
  Assert(children.size() == 2);

  NodeManager* nm = NodeManager::currentNM();
  BvLinearAttribute is_linear;
  Node coeffs[2], leafs[2];
  bool neg;
  TNode child;

  for (unsigned i = 0; i < 2; ++i)
  {
    child = children[i];
    neg = false;
    if (child.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      child = child[0];
    }
    if (child.getAttribute(is_linear) || child == pv)
    {
      if (child.getKind() == BITVECTOR_ADD)
      {
        Assert(isLinearPlus(child, pv, contains_pv));
        coeffs[i] = getPvCoeff(pv, child[0]);
        leafs[i] = child[1];
      }
      else
      {
        Assert(child.getKind() == BITVECTOR_MULT || child == pv);
        coeffs[i] = getPvCoeff(pv, child);
      }
    }
    if (neg)
    {
      if (!coeffs[i].isNull())
      {
        coeffs[i] = nm->mkNode(BITVECTOR_NEG, coeffs[i]);
      }
      if (!leafs[i].isNull())
      {
        leafs[i] = nm->mkNode(BITVECTOR_NEG, leafs[i]);
      }
    }
  }

  if (coeffs[0].isNull() || coeffs[1].isNull())
  {
    return Node::null();
  }

  Node coeff = nm->mkNode(BITVECTOR_SUB, coeffs[0], coeffs[1]);
  coeff = rewrite(coeff);
  std::vector<Node> mult_children = {pv, coeff};
  Node lhs = normalizePvMult(pv, mult_children, contains_pv);

  Node rhs;
  if (!leafs[0].isNull() && !leafs[1].isNull())
  {
    rhs = nm->mkNode(BITVECTOR_SUB, leafs[1], leafs[0]);
  }
  else if (!leafs[0].isNull())
  {
    rhs = nm->mkNode(BITVECTOR_NEG, leafs[0]);
  }
  else if (!leafs[1].isNull())
  {
    rhs = leafs[1];
  }
  else
  {
    rhs = bv::utils::mkZero(bv::utils::getSize(pv));
  }
  rhs = rewrite(rhs);

  if (lhs == rhs)
  {
    return bv::utils::mkTrue();
  }

  Node result = lhs.eqNode(rhs);
  contains_pv[result] = true;
  return result;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
