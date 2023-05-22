/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inverse rules for bit-vector operators.
 */

#include "theory/quantifiers/bv_inverter.h"

#include <algorithm>

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/bv_inverter_utils.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

BvInverter::BvInverter(const Options& opts, Rewriter* r)
    : d_opts(opts), d_rewriter(r)
{
}

/*---------------------------------------------------------------------------*/

Node BvInverter::getSolveVariable(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator its = d_solve_var.find(tn);
  if (its == d_solve_var.end())
  {
    SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
    Node k = sm->mkDummySkolem("slv", tn);
    d_solve_var[tn] = k;
    return k;
  }
  return its->second;
}

/*---------------------------------------------------------------------------*/

Node BvInverter::getInversionNode(Node cond, TypeNode tn, BvInverterQuery* m)
{
  TNode solve_var = getSolveVariable(tn);

  // condition should be rewritten
  Node new_cond = cond;
  if (d_rewriter != nullptr)
  {
    new_cond = d_rewriter->rewrite(cond);
    if (new_cond != cond)
    {
      Trace("cegqi-bv-skvinv-debug")
          << "Condition " << cond << " was rewritten to " << new_cond
          << std::endl;
    }
  }
  // optimization : if condition is ( x = solve_var ) should just return
  // solve_var and not introduce a Skolem this can happen when we ask for
  // the multiplicative inversion with bv1
  Node c;
  if (new_cond.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (new_cond[i] == solve_var)
      {
        c = new_cond[1 - i];
        Trace("cegqi-bv-skvinv")
            << "SKVINV : " << c << " is trivially associated with conditon "
            << new_cond << std::endl;
        break;
      }
    }
  }

  if (c.isNull())
  {
    NodeManager* nm = NodeManager::currentNM();
    if (m)
    {
      Node x = m->getBoundVariable(tn);
      Node ccond = new_cond.substitute(solve_var, x);
      c = nm->mkNode(kind::WITNESS, nm->mkNode(BOUND_VAR_LIST, x), ccond);
      Trace("cegqi-bv-skvinv")
          << "SKVINV : Make " << c << " for " << new_cond << std::endl;
    }
    else
    {
      Trace("bv-invert") << "...fail for " << cond << " : no inverter query!"
                         << std::endl;
    }
  }
  // currently shouldn't cache since
  // the return value depends on the
  // state of m (which bound variable is returned).
  return c;
}

/*---------------------------------------------------------------------------*/

static bool isInvertible(Kind k, unsigned index)
{
  return k == NOT || k == EQUAL || k == BITVECTOR_ULT || k == BITVECTOR_SLT
         || k == BITVECTOR_COMP || k == BITVECTOR_NOT || k == BITVECTOR_NEG
         || k == BITVECTOR_CONCAT || k == BITVECTOR_SIGN_EXTEND
         || k == BITVECTOR_ADD || k == BITVECTOR_MULT || k == BITVECTOR_UREM
         || k == BITVECTOR_UDIV || k == BITVECTOR_AND || k == BITVECTOR_OR
         || k == BITVECTOR_XOR || k == BITVECTOR_LSHR || k == BITVECTOR_ASHR
         || k == BITVECTOR_SHL;
}

Node BvInverter::getPathToPv(Node lit,
                             Node pv,
                             Node sv,
                             std::vector<unsigned>& path,
                             std::unordered_set<TNode>& visited)
{
  if (visited.find(lit) == visited.end())
  {
    visited.insert(lit);
    if (lit == pv)
    {
      return sv;
    }
    else
    {
      unsigned rmod = 0;  // TODO : randomize?
      for (size_t i = 0, num = lit.getNumChildren(); i < num; i++)
      {
        size_t ii = (i + rmod) % lit.getNumChildren();
        // only recurse if the kind is invertible
        // this allows us to avoid paths that go through skolem functions
        if (!isInvertible(lit.getKind(), ii))
        {
          continue;
        }
        Node litc = getPathToPv(lit[ii], pv, sv, path, visited);
        if (!litc.isNull())
        {
          // path is outermost term index last
          path.push_back(ii);
          std::vector<Node> children;
          if (lit.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            children.push_back(lit.getOperator());
          }
          for (size_t j = 0, num2 = lit.getNumChildren(); j < num2; j++)
          {
            children.push_back(j == ii ? litc : lit[j]);
          }
          return NodeManager::currentNM()->mkNode(lit.getKind(), children);
        }
      }
    }
  }
  return Node::null();
}

Node BvInverter::getPathToPv(Node lit,
                             Node pv,
                             Node sv,
                             Node pvs,
                             std::vector<unsigned>& path,
                             bool projectNl)
{
  std::unordered_set<TNode> visited;
  Node slit = getPathToPv(lit, pv, sv, path, visited);
  // if we are able to find a (invertible) path to pv
  if (!slit.isNull() && !pvs.isNull())
  {
    // substitute pvs for the other occurrences of pv
    TNode tpv = pv;
    TNode tpvs = pvs;
    Node prev_lit = slit;
    slit = slit.substitute(tpv, tpvs);
    if (!projectNl && slit != prev_lit)
    {
      // found another occurrence of pv that was not on the solve path,
      // hence lit is non-linear wrt pv and we return null.
      return Node::null();
    }
  }
  return slit;
}

/*---------------------------------------------------------------------------*/

/* Drop child at given index from expression.
 * E.g., dropChild((x + y + z), 1) -> (x + z)  */
static Node dropChild(Node n, unsigned index)
{
  unsigned nchildren = n.getNumChildren();
  Assert(nchildren > 0);
  Assert(index < nchildren);

  if (nchildren < 2) return Node::null();

  Kind k = n.getKind();
  NodeBuilder nb(k);
  for (unsigned i = 0; i < nchildren; ++i)
  {
    if (i == index) continue;
    nb << n[i];
  }
  Assert(nb.getNumChildren() > 0);
  return nb.getNumChildren() == 1 ? nb[0] : nb.constructNode();
}

Node BvInverter::solveBvLit(Node sv,
                            Node lit,
                            std::vector<unsigned>& path,
                            BvInverterQuery* m)
{
  Assert(!path.empty());

  bool pol = true;
  unsigned index;
  NodeManager* nm = NodeManager::currentNM();
  Kind k, litk;

  Assert(!path.empty());
  index = path.back();
  Assert(index < lit.getNumChildren());
  path.pop_back();
  litk = k = lit.getKind();

  /* Note: option --bool-to-bv is currently disabled when CBQI BV
   *       is enabled and the logic is quantified.
   *       We currently do not support Boolean operators
   *       that are interpreted as bit-vector operators of width 1.  */

  /* Boolean layer ----------------------------------------------- */

  if (k == NOT)
  {
    pol = !pol;
    lit = lit[index];
    Assert(!path.empty());
    index = path.back();
    Assert(index < lit.getNumChildren());
    path.pop_back();
    litk = k = lit.getKind();
  }

  Assert(k == EQUAL || k == BITVECTOR_ULT || k == BITVECTOR_SLT);

  Node sv_t = lit[index];
  Node t = lit[1 - index];
  if (litk == BITVECTOR_ULT && index == 1)
  {
    litk = BITVECTOR_UGT;
  }
  else if (litk == BITVECTOR_SLT && index == 1)
  {
    litk = BITVECTOR_SGT;
  }

  /* Bit-vector layer -------------------------------------------- */

  while (!path.empty())
  {
    unsigned nchildren = sv_t.getNumChildren();
    Assert(nchildren > 0);
    index = path.back();
    Assert(index < nchildren);
    path.pop_back();
    k = sv_t.getKind();

    /* Note: All n-ary kinds except for CONCAT (i.e., BITVECTOR_AND,
     *       BITVECTOR_OR, MULT, ADD) are commutative (no case split
     *       based on index). */
    Node s = dropChild(sv_t, index);
    Assert((nchildren == 1 && s.isNull()) || (nchildren > 1 && !s.isNull()));
    TypeNode solve_tn = sv_t[index].getType();
    Node x = getSolveVariable(solve_tn);
    Node ic;

    if (litk == EQUAL && (k == BITVECTOR_NOT || k == BITVECTOR_NEG))
    {
      t = nm->mkNode(k, t);
    }
    else if (litk == EQUAL && k == BITVECTOR_ADD)
    {
      t = nm->mkNode(BITVECTOR_SUB, t, s);
    }
    else if (litk == EQUAL && k == BITVECTOR_XOR)
    {
      t = nm->mkNode(BITVECTOR_XOR, t, s);
    }
    else if (litk == EQUAL && k == BITVECTOR_MULT && s.isConst()
             && bv::utils::getBit(s, 0))
    {
      unsigned w = bv::utils::getSize(s);
      Integer s_val = s.getConst<BitVector>().toInteger();
      Integer mod_val = Integer(1).multiplyByPow2(w);
      Trace("bv-invert-debug")
          << "Compute inverse : " << s_val << " " << mod_val << std::endl;
      Integer inv_val = s_val.modInverse(mod_val);
      Trace("bv-invert-debug") << "Inverse : " << inv_val << std::endl;
      Node inv = bv::utils::mkConst(w, inv_val);
      t = nm->mkNode(BITVECTOR_MULT, inv, t);
    }
    else if (k == BITVECTOR_MULT)
    {
      ic = utils::getICBvMult(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_SHL)
    {
      ic = utils::getICBvShl(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_UREM)
    {
      ic = utils::getICBvUrem(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_UDIV)
    {
      ic = utils::getICBvUdiv(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_AND || k == BITVECTOR_OR)
    {
      ic = utils::getICBvAndOr(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_LSHR)
    {
      ic = utils::getICBvLshr(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_ASHR)
    {
      ic = utils::getICBvAshr(pol, litk, k, index, x, s, t);
    }
    else if (k == BITVECTOR_CONCAT)
    {
      if (litk == EQUAL && d_opts.quantifiers.cegqiBvConcInv)
      {
        /* Compute inverse for s1 o x, x o s2, s1 o x o s2
         * (while disregarding that invertibility depends on si)
         * rather than an invertibility condition (the proper handling).
         * This improves performance on a considerable number of benchmarks.
         *
         * x = t[upper:lower]
         * where
         * upper = getSize(t) - 1 - sum(getSize(sv_t[i])) for i < index
         * lower = getSize(sv_t[i]) for i > index  */
        unsigned upper, lower;
        upper = bv::utils::getSize(t) - 1;
        lower = 0;
        NodeBuilder nb(BITVECTOR_CONCAT);
        for (unsigned i = 0; i < nchildren; i++)
        {
          if (i < index)
          {
            upper -= bv::utils::getSize(sv_t[i]);
          }
          else if (i > index)
          {
            lower += bv::utils::getSize(sv_t[i]);
          }
        }
        t = bv::utils::mkExtract(t, upper, lower);
      }
      else
      {
        ic = utils::getICBvConcat(pol, litk, index, x, sv_t, t);
      }
    }
    else if (k == BITVECTOR_SIGN_EXTEND)
    {
      ic = utils::getICBvSext(pol, litk, index, x, sv_t, t);
    }
    else if (litk == BITVECTOR_ULT || litk == BITVECTOR_UGT)
    {
      ic = utils::getICBvUltUgt(pol, litk, x, t);
    }
    else if (litk == BITVECTOR_SLT || litk == BITVECTOR_SGT)
    {
      ic = utils::getICBvSltSgt(pol, litk, x, t);
    }
    else if (pol == false)
    {
      Assert(litk == EQUAL);
      ic = nm->mkNode(DISTINCT, x, t);
      Trace("bv-invert") << "Add SC_" << litk << "(" << x << "): " << ic
                         << std::endl;
    }
    else
    {
      Trace("bv-invert") << "bv-invert : Unknown kind " << k
                         << " for bit-vector term " << sv_t << std::endl;
      return Node::null();
    }

    if (!ic.isNull())
    {
      /* We generate a witness term (witness x0. ic => x0 <k> s <litk> t) for
       * x <k> s <litk> t. When traversing down, this witness term determines
       * the value for x <k> s = (witness x0. ic => x0 <k> s <litk> t), i.e.,
       * from here on, the propagated literal is a positive equality. */
      litk = EQUAL;
      pol = true;
      /* t = fresh skolem constant */
      t = getInversionNode(ic, solve_tn, m);
      if (t.isNull())
      {
        return t;
      }
    }

    sv_t = sv_t[index];
  }

  /* Base case  */
  Assert(sv_t == sv);
  TypeNode solve_tn = sv.getType();
  Node x = getSolveVariable(solve_tn);
  Node ic;
  if (litk == BITVECTOR_ULT || litk == BITVECTOR_UGT)
  {
    ic = utils::getICBvUltUgt(pol, litk, x, t);
  }
  else if (litk == BITVECTOR_SLT || litk == BITVECTOR_SGT)
  {
    ic = utils::getICBvSltSgt(pol, litk, x, t);
  }
  else if (pol == false)
  {
    Assert(litk == EQUAL);
    ic = nm->mkNode(DISTINCT, x, t);
    Trace("bv-invert") << "Add SC_" << litk << "(" << x << "): " << ic
                       << std::endl;
  }

  return ic.isNull() ? t : getInversionNode(ic, solve_tn, m);
}

/*---------------------------------------------------------------------------*/

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
