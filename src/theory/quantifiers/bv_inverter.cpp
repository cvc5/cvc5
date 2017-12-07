/*********************                                                        */
/*! \file bv_inverter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inverse rules for bit-vector operators
 **/

#include "theory/quantifiers/bv_inverter.h"

#include <algorithm>
#include <stack>

#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/bv/theory_bv_utils.h"


using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

/*---------------------------------------------------------------------------*/

Node BvInverter::getSolveVariable(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator its = d_solve_var.find(tn);
  if (its == d_solve_var.end())
  {
    Node k = NodeManager::currentNM()->mkSkolem("slv", tn);
    d_solve_var[tn] = k;
    return k;
  }
  else
  {
    return its->second;
  }
}

/*---------------------------------------------------------------------------*/

Node BvInverter::getInversionNode(Node cond, TypeNode tn, BvInverterQuery* m)
{
  // condition should be rewritten
  Node new_cond = Rewriter::rewrite(cond);
  if (new_cond != cond)
  {
    Trace("cegqi-bv-skvinv-debug") << "Condition " << cond
                                   << " was rewritten to " << new_cond
                                   << std::endl;
  }
  Node c;
  // optimization : if condition is ( x = v ) should just return v and not
  // introduce a Skolem this can happen when we ask for the multiplicative
  // inversion with bv1
  TNode solve_var = getSolveVariable(tn);
  if (new_cond.getKind() == EQUAL)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (new_cond[i] == solve_var)
      {
        c = new_cond[1 - i];
        Trace("cegqi-bv-skvinv") << "SKVINV : " << c
                                 << " is trivially associated with conditon "
                                 << new_cond << std::endl;
        break;
      }
    }
  }
  // TODO : compute the value if the condition is deterministic, e.g. calc
  // multiplicative inverse of 2 constants
  if (c.isNull())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node x = m->getBoundVariable(tn);
    Node ccond = new_cond.substitute(solve_var, x);
    c = nm->mkNode(kind::CHOICE, nm->mkNode(BOUND_VAR_LIST, x), ccond);
    Trace("cegqi-bv-skvinv") << "SKVINV : Make " << c << " for " << new_cond
                             << std::endl;
  }
  // currently shouldn't cache since
  // the return value depends on the
  // state of m (which bound variable is returned).
  return c;
}

/*---------------------------------------------------------------------------*/

static bool isInvertible(Kind k, unsigned index)
{
  return  k == NOT
      ||  k == EQUAL
      ||  k == BITVECTOR_ULT
      ||  k == BITVECTOR_SLT
      ||  k == BITVECTOR_COMP
      ||  k == BITVECTOR_NOT
      ||  k == BITVECTOR_NEG
      ||  k == BITVECTOR_CONCAT
      ||  k == BITVECTOR_SIGN_EXTEND
      ||  k == BITVECTOR_PLUS
      ||  k == BITVECTOR_SUB
      ||  k == BITVECTOR_MULT
      || (k == BITVECTOR_UREM_TOTAL && index == 1)
      ||  k == BITVECTOR_UDIV_TOTAL
      ||  k == BITVECTOR_AND
      ||  k == BITVECTOR_OR
      ||  k == BITVECTOR_XOR
      || (k == BITVECTOR_LSHR && index == 0)
      || (k == BITVECTOR_ASHR && index == 0)
      || (k == BITVECTOR_SHL && index == 0);
}

Node BvInverter::getPathToPv(
    Node lit,
    Node pv,
    Node sv,
    std::vector<unsigned>& path,
    std::unordered_set<TNode, TNodeHashFunction>& visited)
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
      for (unsigned i = 0; i < lit.getNumChildren(); i++)
      {
        unsigned ii = (i + rmod) % lit.getNumChildren();
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
          for (unsigned j = 0; j < lit.getNumChildren(); j++)
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

Node BvInverter::getPathToPv(
    Node lit, Node pv, Node sv, Node pvs, std::vector<unsigned>& path)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  Node slit = getPathToPv(lit, pv, sv, path, visited);
  // if we are able to find a (invertible) path to pv
  if (!slit.isNull())
  {
    // substitute pvs for the other occurrences of pv
    TNode tpv = pv;
    TNode tpvs = pvs;
    slit = slit.substitute(tpv, tpvs);
  }
  return slit;
}

/*---------------------------------------------------------------------------*/

/* Drop child at given index from expression.
 * E.g., dropChild((x + y + z), 1) -> (x + z)  */
static Node dropChild(Node n, unsigned index)
{
  unsigned nchildren = n.getNumChildren();
  Assert(index < nchildren);
  Kind k = n.getKind();
  Assert(k == BITVECTOR_AND || k == BITVECTOR_OR || k == BITVECTOR_MULT
         || k == BITVECTOR_PLUS);
  NodeBuilder<> nb(NodeManager::currentNM(), k);
  for (unsigned i = 0; i < nchildren; ++i)
  {
    if (i == index) continue;
    nb << n[i];
  }
  return nb.constructNode();
}

static Node getScBvUlt(bool pol, Kind k, unsigned idx, Node x, Node t)
{
  Assert(k == BITVECTOR_ULT);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(t);
  Node sc;

  if (idx == 0)
  {
    if (pol == true)
    {
      /* x < t
       * with side condition:
       * t != 0  */
      Node scl = nm->mkNode(DISTINCT, t, bv::utils::mkZero(w));
      Node scr = nm->mkNode(k, x, t);
      sc = nm->mkNode(IMPLIES, scl, scr);
    }
    else
    {
      sc = nm->mkNode(NOT, nm->mkNode(k, x, t));
    }
  }
  else if (idx == 1)
  {
    if (pol == true)
    {
      /* t < x
       * with side condition:
       * t != ~0  */
      Node scl = nm->mkNode(DISTINCT, t, bv::utils::mkOnes(w));
      Node scr = nm->mkNode(k, t, x);
      sc = nm->mkNode(IMPLIES, scl, scr);
    }
    else
    {
      sc = nm->mkNode(NOT, nm->mkNode(k, t, x));
    }
  }
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvSlt(bool pol, Kind k, unsigned idx, Node x, Node t)
{
  Assert(k == BITVECTOR_SLT);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(t);
  Node sc;

  if (idx == 0)
  {
    if (pol == true)
    {
      /* x < t
       * with side condition:
       * t != 10...0 */
      Node min = bv::utils::mkConst(BitVector(w).setBit(w - 1));
      Node scl = nm->mkNode(DISTINCT, min, t);
      Node scr = nm->mkNode(k, x, t);
      sc = nm->mkNode(IMPLIES, scl, scr);
    }
    else
    {
      sc = nm->mkNode(NOT, nm->mkNode(k, x, t));
    }
  }
  else if (idx == 1)
  {
    if (pol == true)
    {
      /* t < x
       * with side condition:
       * t != 01...1  */
      BitVector bv = BitVector(w).setBit(w - 1);
      Node max = bv::utils::mkConst(~bv);
      Node scl = nm->mkNode(DISTINCT, t, max);
      Node scr = nm->mkNode(k, t, x);
      sc = nm->mkNode(IMPLIES, scl, scr);
    }
    else
    {
      sc = nm->mkNode(NOT, nm->mkNode(k, t, x));
    }
  }
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvEq(bool pol, Kind k, unsigned idx, Node x, Node t)
{
  Assert(k == EQUAL);
  Assert(pol == false);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(t);

  /* x != t
   * <->
   * x < t || x > t  (ULT)
   * with side condition:
   * t != 0 || t != ~0  */
  Node scl = nm->mkNode(OR,
      nm->mkNode(DISTINCT, t, bv::utils::mkZero(w)),
      nm->mkNode(DISTINCT, t, bv::utils::mkOnes(w)));
  Node scr = nm->mkNode(DISTINCT, x, t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvMult(Kind k, unsigned idx, Node x, Node s, Node t)
{
  Assert(k == BITVECTOR_MULT);

  NodeManager* nm = NodeManager::currentNM();

  /* x * s = t
   * with side condition:
   * ctz(t) >= ctz(s) <-> x * s = t
   * where
   * ctz(t) >= ctz(s) -> t = 0 \/ ((t & -t) >= (s & -s) /\ s != 0) */
  Node zero = bv::utils::mkZero(bv::utils::getSize(s));
  Node t_uge_s = nm->mkNode(BITVECTOR_UGE,
      nm->mkNode(BITVECTOR_AND, t, nm->mkNode(BITVECTOR_NEG, t)),
      nm->mkNode(BITVECTOR_AND, s, nm->mkNode(BITVECTOR_NEG, s)));
  Node scl = nm->mkNode(OR,
      t.eqNode(zero),
      nm->mkNode(AND, t_uge_s, s.eqNode(zero).notNode()));
  Node scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvUrem(Kind k, unsigned idx, Node x, Node s, Node t)
{
  Assert(k == BITVECTOR_UREM_TOTAL);
  Assert(idx == 1);

  NodeManager* nm = NodeManager::currentNM();

  /* s % x = t
   * with side condition:
   * s = t
   * ||
   * ( s > t
   *   && s-t > t
   *   && (t = 0 || t != s-1) )  */

  Node a1 =  // s > t
    nm->mkNode(BITVECTOR_UGT, s, t);
  Node a2 =  // s-t > t
    nm->mkNode(BITVECTOR_UGT, nm->mkNode(BITVECTOR_SUB, s, t), t);
  Node a3 =  // (t = 0 || t != s-1)
    nm->mkNode(OR,
        t.eqNode(bv::utils::mkZero(bv::utils::getSize(t))),
        t.eqNode(bv::utils::mkDec(s)).notNode());

  Node scl = nm->mkNode(OR,
        t.eqNode(s),
        nm->mkNode(AND, a1, nm->mkNode(AND, a2, a3)));
  Node scr = nm->mkNode(EQUAL, nm->mkNode(k, s, x), t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);

  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvUdiv(Kind k, unsigned idx, Node x, Node s, Node t)
{
  Assert(k == BITVECTOR_UDIV_TOTAL);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(s);
  Assert (w == bv::utils::getSize(t));
  Node scl, scr;
  Node zero = bv::utils::mkZero(w);

  if (idx == 0)
  {
    /* x udiv s = t
     * with side condition:
     * t = ~0 && (s = 0 || s = 1)
     * ||
     * (t != ~0 && s != 0 && !umulo(s * t)) */
    Node o1 = nm->mkNode(AND,
        t.eqNode(bv::utils::mkOnes(w)),
        nm->mkNode(OR,
          s.eqNode(bv::utils::mkZero(w)),
          s.eqNode(bv::utils::mkOne(w))));
    Node o2 = nm->mkNode(AND,
        t.eqNode(bv::utils::mkOnes(w)).notNode(),
        s.eqNode(bv::utils::mkZero(w)).notNode(),
        nm->mkNode(NOT, bv::utils::mkUmulo(s, t)));

    scl = nm->mkNode(OR, o1, o2);
    scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
  }
  else
  {
    /* s udiv x = t
     * with side condition:
     * s = t
     * ||
     * t = ~0
     * ||
     * (s >= t
     *  && (s % t = 0 || (s / (t+1) +1) <= s / t)
     *  && (s = ~0 => t != 0))  */

    Node oo1 = nm->mkNode(EQUAL,
        nm->mkNode(BITVECTOR_UREM_TOTAL, s, t),
        bv::utils::mkZero(w));

    Node ule1 = nm->mkNode(BITVECTOR_PLUS,
        bv::utils::mkOne(w),
        nm->mkNode(BITVECTOR_UDIV_TOTAL,
          s, nm->mkNode(BITVECTOR_PLUS, t, bv::utils::mkOne(w))));
    Node ule2 = nm->mkNode(BITVECTOR_UDIV_TOTAL, s, t);
    Node oo2 = nm->mkNode(BITVECTOR_ULE, ule1, ule2);

    Node a1 = nm->mkNode(BITVECTOR_UGE, s, t);
    Node a2 = nm->mkNode(OR, oo1, oo2);
    Node a3 = nm->mkNode(IMPLIES,
        s.eqNode(bv::utils::mkOnes(w)),
        t.eqNode(bv::utils::mkZero(w)).notNode());

    Node o1 = s.eqNode(t);
    Node o2 = t.eqNode(bv::utils::mkOnes(w));
    Node o3 = nm->mkNode(AND, a1, a2, a3);

    scl = nm->mkNode(OR, o1, o2, o3);
    scr = nm->mkNode(EQUAL, nm->mkNode(k, s, x), t);
  }

  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvAndOr(Kind k, unsigned idx, Node x, Node s, Node t)
{
  NodeManager* nm = NodeManager::currentNM();
  /* with side condition:
   * t & s = t
   * t | s = t */
  Node scl = nm->mkNode(EQUAL, t, nm->mkNode(k, t, s));
  Node scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvLshr(Kind k, unsigned idx, Node x, Node s, Node t)
{
  Assert(k == BITVECTOR_LSHR);
  Assert(idx == 0);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(s);
  Assert(w == bv::utils::getSize(t));
  
  /* x >> s = t
   * with side condition:
   * s = 0 || (s < w && clz(t) >=s) || (s >= w && t = 0)
   * ->
   * s = 0 || (s < w && ((z o t) << (z o s))[2w-1 : w] = z) || (s >= w && t = 0)
   * with w = getSize(t) = getSize(s)
   * and z = 0 with getSize(z) = w  */

  Node z = bv::utils::mkZero(w);
  Node ww = bv::utils::mkConst(w, w);

  Node z_o_t = nm->mkNode(BITVECTOR_CONCAT, z, t);
  Node z_o_s = nm->mkNode(BITVECTOR_CONCAT, z, s);
  Node shl = nm->mkNode(BITVECTOR_SHL, z_o_t, z_o_s);
  Node ext = bv::utils::mkExtract(shl, 2*w-1, w);

  Node o1 = s.eqNode(z);
  Node o2 = nm->mkNode(AND, nm->mkNode(BITVECTOR_ULT, s, ww), ext.eqNode(z));
  Node o3 = nm->mkNode(AND, nm->mkNode(BITVECTOR_UGE, s, ww), t.eqNode(z));

  Node scl = nm->mkNode(OR, o1, o2, o3);
  Node scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvAshr(Kind k, unsigned idx, Node x, Node s, Node t)
{
  Assert(k == BITVECTOR_ASHR);
  Assert(idx == 0);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(s);
  Assert(w == bv::utils::getSize(t));
  
  /* x >> s = t
   * with side condition:
   * s = 0
   * ||
   * (s < w && (((z o t) << (z o s))[2w-1:w-1] = z
   *            ||
   *            ((~z o t) << (z o s))[2w-1:w-1] = ~z))
   * ||
   * (s >= w && (t = 0 || t = ~0))
   * with w = getSize(t) = getSize(s)
   * and z = 0 with getSize(z) = w  */
  
  Node z = bv::utils::mkZero(w);
  Node zz = bv::utils::mkZero(w+1);
  Node n = bv::utils::mkOnes(w);
  Node nn = bv::utils::mkOnes(w+1);
  Node ww = bv::utils::mkConst(w, w);

  Node z_o_t = bv::utils::mkConcat(z, t);
  Node z_o_s = bv::utils::mkConcat(z, s);
  Node n_o_t = bv::utils::mkConcat(n, t);

  Node shlz = nm->mkNode(BITVECTOR_SHL, z_o_t, z_o_s);
  Node shln = nm->mkNode(BITVECTOR_SHL, n_o_t, z_o_s);
  Node extz = bv::utils::mkExtract(shlz, 2*w-1, w-1);
  Node extn = bv::utils::mkExtract(shln, 2*w-1, w-1);

  Node o1 = s.eqNode(z);
  Node o2 = nm->mkNode(AND,
      nm->mkNode(BITVECTOR_ULT, s, ww),
      nm->mkNode(OR, extz.eqNode(zz), extn.eqNode(nn)));
  Node o3 = nm->mkNode(AND,
      nm->mkNode(BITVECTOR_UGE, s, ww),
      nm->mkNode(OR, t.eqNode(z), t.eqNode(n)));

  Node scl = nm->mkNode(OR, o1, o2, o3);
  Node scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvShl(Kind k, unsigned idx, Node x, Node s, Node t)
{
  Assert(k == BITVECTOR_SHL);
  Assert(idx == 0);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(s);
  Assert(w == bv::utils::getSize(t));

  /* x << s = t
   * with side condition:
   * (s = 0 || ctz(t) >= s)
   * <->
   * (s = 0 || (s < w && ((t o z) >> (z o s))[w-1:0] = z) || (s >= w && t = 0)
   *
   * where
   * w = getSize(s) = getSize(t) = getSize (z) && z = 0
   */

  Node z = bv::utils::mkConst(w, 0u);
  Node ww = bv::utils::mkConst(w, w);

  Node shr = nm->mkNode(BITVECTOR_LSHR,
      bv::utils::mkConcat(t, z),
      bv::utils::mkConcat(z, s));
  Node ext = bv::utils::mkExtract(shr, w - 1, 0);

  Node o1 = nm->mkNode(EQUAL, s, z);
  Node o2 = nm->mkNode(AND, nm->mkNode(BITVECTOR_ULT, s, ww), ext.eqNode(z));
  Node o3 = nm->mkNode(AND, nm->mkNode(BITVECTOR_UGE, s, ww), t.eqNode(z));

  Node scl = nm->mkNode(OR, o1, o2, o3);
  Node scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

Node BvInverter::solveBvLit(Node sv,
                            Node lit,
                            std::vector<unsigned>& path,
                            BvInverterQuery* m,
                            BvInverterStatus& status)
{
  Assert(!path.empty());

  bool pol = true;
  unsigned index, nchildren;
  NodeManager* nm = NodeManager::currentNM();
  Kind k;

  Assert(!path.empty());
  index = path.back();
  Assert(index < lit.getNumChildren());
  path.pop_back();
  k = lit.getKind();
  
  /* Note: option --bool-to-bv is currently disabled when CBQI BV
   *       is enabled. We currently do not support Boolean operators
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
    k = lit.getKind();
  }

  Assert(k == EQUAL
      || k == BITVECTOR_ULT
      || k == BITVECTOR_SLT
      || k == BITVECTOR_COMP);

  Node sv_t = lit[index];
  Node t = lit[1-index];

  switch (k)
  {
    case BITVECTOR_ULT:
    {
      TypeNode solve_tn = sv_t.getType();
      Node sc = getScBvUlt(pol, k, index, getSolveVariable(solve_tn), t);
      /* t = fresh skolem constant  */
      t = getInversionNode(sc, solve_tn, m);
      if (!path.empty())
      {
        index = path.back();
        Assert(index < sv_t.getNumChildren());
        path.pop_back();
        sv_t = sv_t[index];
        k = sv_t.getKind();
      }
      break;
    }

    case BITVECTOR_SLT:
    {
      TypeNode solve_tn = sv_t.getType();
      Node sc = getScBvSlt(pol, k, index, getSolveVariable(solve_tn), t);
      /* t = fresh skolem constant  */
      t = getInversionNode(sc, solve_tn, m);
      if (!path.empty())
      {
        index = path.back();
        Assert(index < sv_t.getNumChildren());
        path.pop_back();
        sv_t = sv_t[index];
        k = sv_t.getKind();
      }
      break;
    }

    default:
      Assert(k == EQUAL);
      if (pol == false)
      {
        TypeNode solve_tn = sv_t.getType();
        Node sc = getScBvEq(pol, k, index, getSolveVariable(solve_tn), t);
        /* t = fresh skolem constant  */
        t = getInversionNode(sc, solve_tn, m);
        if (!path.empty())
        {
          index = path.back();
          Assert(index < sv_t.getNumChildren());
          path.pop_back();
          sv_t = sv_t[index];
          k = sv_t.getKind();
        }
      }
  }

  /* Bit-vector layer -------------------------------------------- */

  while (!path.empty())
  {
    index = path.back();
    Assert(index < sv_t.getNumChildren());
    path.pop_back();
    k = sv_t.getKind();
    nchildren = sv_t.getNumChildren();

    if (k == BITVECTOR_NOT || k == BITVECTOR_NEG)
    {
      t = nm->mkNode(k, t);
    }
    else if (k == BITVECTOR_CONCAT)
    {
      /* x = t[upper:lower]
       * where
       * upper = getSize(t) - 1 - sum(getSize(sv_t[i])) for i < index
       * lower = getSize(sv_t[i]) for i > index
       */
      unsigned upper, lower;
      upper = bv::utils::getSize(t) - 1;
      lower = 0;
      NodeBuilder<> nb(nm, BITVECTOR_CONCAT);
      for (unsigned i = 0; i < nchildren; i++)
      {
        if (i < index) { upper -= bv::utils::getSize(sv_t[i]); }
        else if (i > index) { lower += bv::utils::getSize(sv_t[i]); }
      }
      t = bv::utils::mkExtract(t, upper, lower);
    }
    else if (k == BITVECTOR_SIGN_EXTEND)
    {
      t = bv::utils::mkExtract(t, bv::utils::getSize(sv_t[index]) - 1, 0);
    }
    else if (k == BITVECTOR_EXTRACT)
    {
      Trace("bv-invert") << "bv-invert : Unsupported for index " << index
                         << ", from " << sv_t << std::endl;
      return Node::null();
    }
    else
    {
      Assert(nchildren >= 2);
      Node s = nchildren == 2 ? sv_t[1 - index] : dropChild(sv_t, index);
      /* Note: All n-ary kinds except for CONCAT (i.e., AND, OR, MULT, PLUS)
       *       are commutative (no case split based on index). */
      switch (k)
      {
        case BITVECTOR_COMP:
          t = s;
          break;

        case BITVECTOR_PLUS:
          t = nm->mkNode(BITVECTOR_SUB, t, s);
          break;

        case BITVECTOR_SUB:
          t = nm->mkNode(BITVECTOR_PLUS, t, s);
          break;

        case BITVECTOR_MULT:
        {
          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvMult(k, index, getSolveVariable(solve_tn), s, t);
          /* t = fresh skolem constant */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        case BITVECTOR_UREM_TOTAL:
        {
          if (index == 0)
          {
            /* x % s = t is rewritten to x - x / y * y */
            Trace("bv-invert") << "bv-invert : Unsupported for index " << index
                               << ", from " << sv_t << std::endl;
            return Node::null();
          }
          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvUrem(k, index, getSolveVariable(solve_tn), s, t);
          /* t = skv (fresh skolem constant)  */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        case BITVECTOR_UDIV_TOTAL:
        {
          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvUdiv(k, index, getSolveVariable(solve_tn), s, t);
          /* t = fresh skolem constant */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        case BITVECTOR_AND:
        case BITVECTOR_OR:
        {
          /* with side condition:
           * t & s = t
           * t | s = t */
          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvAndOr(k, index, getSolveVariable(solve_tn), s, t);
          /* t = fresh skolem constant  */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        case BITVECTOR_XOR:
          t = nm->mkNode(BITVECTOR_XOR, t, s);
          break;

        case BITVECTOR_LSHR:
        {
          if (index == 1)
          {
            /* s >> x = t
             * with side condition:
             * clz(t) >= clz(s)
             *   && (t = 0
             *    || "remaining shifted bits in t "
             *       "match corresponding bits in s")  */
            Trace("bv-invert") << "bv-invert : Unsupported for index " << index
                               << ", from " << sv_t << std::endl;
            return Node::null();
          }

          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvLshr(k, index, getSolveVariable(solve_tn), s, t);
          /* t = fresh skolem constant  */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        case BITVECTOR_ASHR:
        {
          if (index == 1)
          {
            /* s >> x = t
             * with side condition:
             * clx(msb(s),t) >= clx(msb(s),s)
             *   && (t = 0
             *    || t = ~0
             *    || "remaining shifted bits in t "
             *          "match corresponding bits in s")  */

            Trace("bv-invert") << "bv-invert : Unsupported for index " << index
                               << ", from " << sv_t << std::endl;
            return Node::null();
          }
          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvAshr(k, index, getSolveVariable(solve_tn), s, t);
          /* t = fresh skolem constant  */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        case BITVECTOR_SHL:
        {
          if (index == 1)
          {
            /* s << x = t
             * with side condition:
             * ctz(t) >= ctz(s)
             * && (t = 0 ||
             *     "remaining shifted bits in t"
             *     "match corresponding bits in s")
             */
            Trace("bv-invert") << "bv-invert : Unsupported for index " << index
                               << "for bit-vector term " << sv_t << std::endl;
            return Node::null();
          }
          TypeNode solve_tn = sv_t[index].getType();
          Node sc = getScBvShl(k, index, getSolveVariable(solve_tn), s, t);
          /* t = fresh skolem constant */
          t = getInversionNode(sc, solve_tn, m);
          break;
        }

        default:
          Trace("bv-invert") << "bv-invert : Unknown kind " << k
                             << " for bit-vector term " << sv_t << std::endl;
          return Node::null();
      }
    }
    sv_t = sv_t[index];
  }
  Assert(sv_t == sv);
  return t;
}

/*---------------------------------------------------------------------------*/

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
