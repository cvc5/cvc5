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
  TNode solve_var = getSolveVariable(tn);

  // condition should be rewritten
  Node new_cond = Rewriter::rewrite(cond);
  if (new_cond != cond)
  {
    Trace("cegqi-bv-skvinv-debug") << "Condition " << cond
                                   << " was rewritten to " << new_cond
                                   << std::endl;
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
      ||  k == BITVECTOR_UREM_TOTAL
      ||  k == BITVECTOR_UDIV_TOTAL
      ||  k == BITVECTOR_AND
      ||  k == BITVECTOR_OR
      ||  k == BITVECTOR_XOR
      || k == BITVECTOR_LSHR
      || k == BITVECTOR_ASHR
      || k == BITVECTOR_SHL;
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
      /* x >= t
       * no side condition  */
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
      /* t >= x
       * no side condition */
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
      /* x >= t
       * no side condition */
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
      /* t >= x
       * no side condition */
      sc = nm->mkNode(NOT, nm->mkNode(k, t, x));
    }
  }
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvMult(bool pol,
                        Kind litk,
                        Kind k,
                        unsigned idx,
                        Node x,
                        Node s,
                        Node t)
{
  Assert(k == BITVECTOR_MULT);

  NodeManager* nm = NodeManager::currentNM();
  Node scl, scr;
  Node z = bv::utils::mkZero(bv::utils::getSize(s));

  if (litk == EQUAL)
  {
    if (pol)
    {
      /* x * s = t
       * with side condition:
       * ctz(t) >= ctz(s) <-> x * s = t
       * where
       * ctz(t) >= ctz(s) -> t = 0 \/ ((t & -t) >= (s & -s) /\ s != 0) */
      Node t_uge_s = nm->mkNode(BITVECTOR_UGE,
          nm->mkNode(BITVECTOR_AND, t, nm->mkNode(BITVECTOR_NEG, t)),
          nm->mkNode(BITVECTOR_AND, s, nm->mkNode(BITVECTOR_NEG, s)));
      scl = nm->mkNode(OR,
          t.eqNode(z),
          nm->mkNode(AND, t_uge_s, s.eqNode(z).notNode()));
      scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
    }
    else
    {
      /* x * s != t
       * with side condition:
       * t != 0 || s != 0 */
      scl = nm->mkNode(OR, t.eqNode(z).notNode(), s.eqNode(z).notNode());
      scr = nm->mkNode(DISTINCT, nm->mkNode(k, x, s), t);
    }
  }
  else
  {
    return Node::null();
  }

  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvUrem(bool pol,
                        Kind litk,
                        Kind k,
                        unsigned idx,
                        Node x,
                        Node s,
                        Node t)
{
  Assert(k == BITVECTOR_UREM_TOTAL);
  Assert (litk == EQUAL || litk == BITVECTOR_ULT || litk == BITVECTOR_SLT);

  NodeManager* nm = NodeManager::currentNM();
  Node scl;
  unsigned w = bv::utils::getSize(s);
  Assert (w == bv::utils::getSize(t));
  Node z = bv::utils::mkZero(w);

  if (litk == EQUAL)
  {
    if (idx == 0)
    {
      if (pol)
      {
        /* x % s = t
         * with side condition (synthesized):
         * (not (bvult (bvnot (bvneg s)) t)) 
         * <->
         * ~(-s) >= t*/
        Node neg = nm->mkNode(BITVECTOR_NEG, s);
        scl = nm->mkNode(BITVECTOR_UGE, nm->mkNode(BITVECTOR_NOT, neg), t);
      }
      else
      {
        /* x % s != t
         * with side condition:
         * s != 1 || t != 0  */
        scl = nm->mkNode(OR,
            s.eqNode(bv::utils::mkOne(w)).notNode(),
            t.eqNode(z).notNode());
      }
    }
    else
    {
      if (pol)
      {
        /* s % x = t
         * with side condition (synthesized):
         * (bvuge (bvand (bvsub (bvadd t t) s) s) t)
         * <->
         * (t + t - s) & s >= t
         *
         * is equivalent to:
         * s = t
         * ||
         * ( s > t
         *   && s-t > t
         *   && (t = 0 || t != s-1) )  */
        Node add = nm->mkNode(BITVECTOR_PLUS, t, t);
        Node sub = nm->mkNode(BITVECTOR_SUB, add, s);
        Node a = nm->mkNode(BITVECTOR_AND, sub, s);
        scl = nm->mkNode(BITVECTOR_UGE, a, t);
      }
      else
      {
        /* s % x != t
         * with side condition:
         * s != 0 || t != 0  */
        scl = nm->mkNode(OR, s.eqNode(z).notNode(), t.eqNode(z).notNode());
      }
    }
  }
  else if (litk == BITVECTOR_ULT)
  {
    if (idx == 0)
    {
      if (pol)
      {
        /* x % s < t
         * with side condition:
         * (distinct t z)
         * where z = 0 with getSize(z) = w  */
        scl = t.eqNode(z).notNode();
      }
      else
      {
        /* x % s >= t
         * with side condition (synthesized):
         * (bvuge (bvnot (bvneg s)) t)  */
        Node neg = nm->mkNode(BITVECTOR_NEG, s);
        scl = nm->mkNode(BITVECTOR_UGE, nm->mkNode(BITVECTOR_NOT, neg), t);
      }
    }
    else
    {
      if (pol)
      {
        /* s % x < t
         * with side condition:
         * (distinct t z)
         * where z = 0 with getSize(z) = w  */
        scl = t.eqNode(z).notNode();
      }
      else
      {
        /* s % x < t
         * with side condition (combination of = and >):
         * (or
         *   (bvuge (bvand (bvsub (bvadd t t) s) s) t)  ; eq, synthesized
         *   (bvult t s))                               ; ugt, synthesized  */
        Node add = nm->mkNode(BITVECTOR_PLUS, t, t);
        Node sub = nm->mkNode(BITVECTOR_SUB, add, s);
        Node a = nm->mkNode(BITVECTOR_AND, sub, s);
        Node sceq = nm->mkNode(BITVECTOR_UGE, a, t);
        Node scugt = nm->mkNode(BITVECTOR_ULT, t, s);
        scl = nm->mkNode(OR, sceq, scugt);
      }
    }
  }
  else  /* litk == BITVECTOR_SLT  */
  {
    if (idx == 0)
    {
      if (pol)
      {
        /* x % s < t
         * with side condition (synthesized):
         * (bvslt (bvnot t) (bvor (bvneg s) (bvneg t)))  */
        Node o1 = nm->mkNode(BITVECTOR_NEG, s);
        Node o2 = nm->mkNode(BITVECTOR_NEG, t);
        Node o = nm->mkNode(BITVECTOR_OR, o1, o2);
        scl = nm->mkNode(BITVECTOR_SLT, nm->mkNode(BITVECTOR_NOT, t), o);
      }
      else
      {
        /* x % s >= t
         * with side condition (synthesized):
         * (or (bvslt t s) (bvsge z s))
         * where z = 0 with getSize(z) = w  */
        Node s1 = nm->mkNode(BITVECTOR_SLT, t, s);
        Node s2 = nm->mkNode(BITVECTOR_SGE, z, s);
        scl = nm->mkNode(OR, s1, s2);
      }
    }
    else
    {
      if (pol)
      {
        /* s % x < t
         * with side condition (synthesized):
         * (or (bvslt s t) (bvslt z t))
         * where z = 0 with getSize(z) = w  */
        Node slt1 = nm->mkNode(BITVECTOR_SLT, s, t);
        Node slt2 = nm->mkNode(BITVECTOR_SLT, z, t);
        scl = nm->mkNode(OR, slt1, slt2);
      }
      else
      {
        /* s % x < t
         * with side condition:
         * (and
         *   (=> (bvsge s z) (bvsge s t))
         *   (=> (and (bvslt s z) (bvsge t z)) (bvugt (bvsub s t) t)))
         * where z = 0 with getSize(z) = w  */
        Node i1 = nm->mkNode(IMPLIES,
            nm->mkNode(BITVECTOR_SGE, s, z), nm->mkNode(BITVECTOR_SGE, s, t));
        Node i2 = nm->mkNode(IMPLIES,
            nm->mkNode(AND,
              nm->mkNode(BITVECTOR_SLT, s, z), nm->mkNode(BITVECTOR_SGE, t, z)),
            nm->mkNode(BITVECTOR_UGT, nm->mkNode(BITVECTOR_SUB, s, t), t));
        scl = nm->mkNode(AND, i1, i2);
      }
    }
  }

  Node scr =
    nm->mkNode(litk, idx == 0 ? nm->mkNode(k, x, s) : nm->mkNode(k, s, x), t);
  Node sc = nm->mkNode(IMPLIES, scl, pol ? scr : scr.notNode());
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvUdiv(bool pol,
                        Kind litk,
                        Kind k,
                        unsigned idx,
                        Node x,
                        Node s,
                        Node t)
{
  Assert(k == BITVECTOR_UDIV_TOTAL);

  NodeManager* nm = NodeManager::currentNM();
  unsigned w = bv::utils::getSize(s);
  Assert (w == bv::utils::getSize(t));
  Node sc, scl, scr;
  Node z = bv::utils::mkZero(w);
  Node n = bv::utils::mkOnes(w);

  if (litk == EQUAL)
  {
    if (idx == 0)
    {
      if (pol)
      {
        /* x udiv s = t
         * with side condition:
         * t = ~0 && (s = 0 || s = 1)
         * ||
         * (t != ~0 && s != 0 && !umulo(s * t)) */
        Node one = bv::utils::mkOne(w);
        Node o1 = nm->mkNode(AND,
            t.eqNode(n),
            nm->mkNode(OR, s.eqNode(z), s.eqNode(one)));
        Node o2 = nm->mkNode(AND,
            t.eqNode(n).notNode(),
            s.eqNode(z).notNode(),
            nm->mkNode(NOT, bv::utils::mkUmulo(s, t)));

        scl = nm->mkNode(OR, o1, o2);
        scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
      }
      else
      {
        /* x udiv s != t
         * with side condition:
         * s != 0 || t != ~0  */
        scl = nm->mkNode(OR, s.eqNode(z).notNode(), t.eqNode(n).notNode());
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, x, s), t);
      }
      sc = nm->mkNode(IMPLIES, scl, scr);
    }
    else
    {
      if (pol)
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
        Node oo1 = nm->mkNode(EQUAL, nm->mkNode(BITVECTOR_UREM_TOTAL, s, t), z); 
        Node udiv = nm->mkNode(BITVECTOR_UDIV_TOTAL, s, bv::utils::mkInc(t));
        Node ule1 = bv::utils::mkInc(udiv);
        Node ule2 = nm->mkNode(BITVECTOR_UDIV_TOTAL, s, t);
        Node oo2 = nm->mkNode(BITVECTOR_ULE, ule1, ule2);

        Node a1 = nm->mkNode(BITVECTOR_UGE, s, t);
        Node a2 = nm->mkNode(OR, oo1, oo2);
        Node a3 = nm->mkNode(IMPLIES, s.eqNode(n), t.eqNode(z).notNode());

        Node o1 = s.eqNode(t);
        Node o2 = t.eqNode(n);
        Node o3 = nm->mkNode(AND, a1, a2, a3);

        scl = nm->mkNode(OR, o1, o2, o3);
        scr = nm->mkNode(EQUAL, nm->mkNode(k, s, x), t);
        sc = nm->mkNode(IMPLIES, scl, scr);
      }
      else
      {
        sc = nm->mkNode(DISTINCT, nm->mkNode(k, s, x), t);
      }
    }
  }
  else
  {
    return Node::null();
  }

  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvAndOr(bool pol,
                         Kind litk,
                         Kind k,
                         unsigned idx,
                         Node x,
                         Node s,
                         Node t)
{
  Assert (k == BITVECTOR_AND || k == BITVECTOR_OR);
  Assert (litk == EQUAL || litk == BITVECTOR_SLT || litk == BITVECTOR_ULT);

  NodeManager* nm = NodeManager::currentNM();
  Node scl, scr;

  if (litk == EQUAL)
  {
    if (pol)
    {
      /* x & s = t
       * x | s = t
       * with side condition:
       * t & s = t
       * t | s = t */
      scl = nm->mkNode(EQUAL, t, nm->mkNode(k, t, s));
    }
    else
    {
      unsigned w = bv::utils::getSize(s);
      Assert (w == bv::utils::getSize(t));

      if (k == BITVECTOR_AND)
      {
        /* x & s = t
         * with side condition:
         * s != 0 || t != 0  */
        Node z = bv::utils::mkZero(w);
        scl = nm->mkNode(OR, s.eqNode(z).notNode(), t.eqNode(z).notNode());
      }
      else
      {
        /* x | s = t
         * with side condition:
         * s != ~0 || t != ~0  */
        Node n = bv::utils::mkOnes(w);
        scl = nm->mkNode(OR, s.eqNode(n).notNode(), t.eqNode(n).notNode());
      }
    }
  }
  else if (litk == BITVECTOR_ULT)
  {
    if (pol)
    {
      if (k == BITVECTOR_AND)
      {
        /* x & s < t
         * with side condition (synthesized):
         * t != 0 */
        Node z = bv::utils::mkZero(bv::utils::getSize(t));
        scl = t.eqNode(z).notNode();
      }
      else
      {
        /* x | s < t
         * with side condition (synthesized):
         * (bvult s t) */
        scl = nm->mkNode(BITVECTOR_ULT, s, t);
      }
    }
    else
    {
      if (k == BITVECTOR_AND)
      {
        /* x & s >= t
         * with side condition (synthesized):
         * (not (bvult s t)) */
        scl = nm->mkNode(BITVECTOR_UGE, s, t);
      }
      else
      {
        /* x | s >= t
         * with side condition (synthesized):
         * true (no side condition) */
        scl = nm->mkConst<bool>(true);
      }
    }
  }
  else if (litk == BITVECTOR_SLT)
  {
    if (pol)
    {
      if (k == BITVECTOR_AND)
      {
        /* x & s < t
         * with side condition (synthesized):
         * (bvslt (bvand (bvnot (bvneg t)) s) t) */
        Node nnt = nm->mkNode(BITVECTOR_NOT, nm->mkNode(BITVECTOR_NEG, t));
        scl = nm->mkNode(BITVECTOR_SLT, nm->mkNode(BITVECTOR_AND, nnt, s), t);
      }
      else
      {
        /* x | s < t
         * with side condition (synthesized):
         * (bvslt (bvor (bvnot (bvsub s t)) s) t) */
        Node st = nm->mkNode(BITVECTOR_NOT, nm->mkNode(BITVECTOR_SUB, s, t));
        scl = nm->mkNode(BITVECTOR_SLT, nm->mkNode(BITVECTOR_OR, st, s), t);
      }
    }
    else
    {
      if (k == BITVECTOR_AND)
      {
        /* x & s >= t
         * with side condition (case = combined with synthesized bvsgt):
         * (or
         *  (= (bvand s t) t)
         *  (bvslt t (bvand (bvsub t s) s))
         * ) */
        Node sc_sgt = nm->mkNode(
            BITVECTOR_SLT,
            t,
            nm->mkNode(BITVECTOR_AND, nm->mkNode(BITVECTOR_SUB, t, s), s));
        Node sc_eq = nm->mkNode(BITVECTOR_AND, s, t).eqNode(t);
        scl = sc_eq.orNode(sc_sgt);
      }
      else
      {
        /* x | s >= t
         * with side condition (synthesized):
         * (not (bvslt s (bvand s t))) */
        scl = nm->mkNode(BITVECTOR_SGE, s, nm->mkNode(BITVECTOR_AND, s, t));
      }
    }
  }
  else
  {
    return Node::null();
  }

  scr = nm->mkNode(litk, nm->mkNode(k, x, s), t);
  Node sc = nm->mkNode(IMPLIES, scl, pol ? scr : scr.notNode());
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvLshr(bool pol,
                        Kind litk,
                        Kind k,
                        unsigned idx,
                        Node x,
                        Node s,
                        Node t)
{
  Assert(k == BITVECTOR_LSHR);

  NodeManager* nm = NodeManager::currentNM();
  Node scl, scr;
  unsigned w = bv::utils::getSize(s);
  Assert(w == bv::utils::getSize(t));
  Node z = bv::utils::mkZero(w);

  if (litk == EQUAL)
  {
    if (idx == 0)
    {
      Node ww = bv::utils::mkConst(w, w);

      if (pol)
      {
        /* x >> s = t
         * with side condition:
         * s = 0 || (s < w && clz(t) >=s) || (s >= w && t = 0)
         * ->
         * s = 0
         * || (s < w && ((z o t) << (z o s))[2w-1 : w] = z)
         * || (s >= w && t = 0)
         * with w = getSize(t) = getSize(s)
         * and z = 0 with getSize(z) = w  */
        Node z_o_t = nm->mkNode(BITVECTOR_CONCAT, z, t);
        Node z_o_s = nm->mkNode(BITVECTOR_CONCAT, z, s);
        Node shl = nm->mkNode(BITVECTOR_SHL, z_o_t, z_o_s);
        Node ext = bv::utils::mkExtract(shl, 2*w-1, w);

        Node o1 = s.eqNode(z);
        Node o2 = nm->mkNode(AND,
            nm->mkNode(BITVECTOR_ULT, s, ww), ext.eqNode(z));
        Node o3 = nm->mkNode(AND,
            nm->mkNode(BITVECTOR_UGE, s, ww), t.eqNode(z));

        scl = nm->mkNode(OR, o1, o2, o3);
        scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
      }
      else
      {
        /* x >> s != t
         * with side condition:
         * t != 0 || s < w
         * with
         * w = getSize(s) = getSize(t)
         */
        scl = nm->mkNode(OR,
            t.eqNode(z).notNode(),
            nm->mkNode(BITVECTOR_ULT, s, ww));
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, x, s), t);
      }
    }
    else
    {
      if (pol)
      {
        /* s >> x = t
         * with side condition:
         * t = 0
         * ||
         * s = t
         * || 
         * \/ (t[w-1-i:0] = s[w-1:i] && t[w-1:w-i] = 0) for 0 < i < w
         * where
         * w = getSize(s) = getSize(t)
         */
        NodeBuilder<> nb(nm, OR);
        nb << nm->mkNode(EQUAL, t, s);
        for (unsigned i = 1; i < w; ++i)
        {
          nb << nm->mkNode(AND,
              nm->mkNode(EQUAL,
                bv::utils::mkExtract(t, w - 1 - i, 0),
                bv::utils::mkExtract(s, w - 1, i)),
              nm->mkNode(EQUAL,
                bv::utils::mkExtract(t, w - 1, w - i),
                bv::utils::mkZero(i)));
        }
        nb << t.eqNode(z);
        scl = nb.constructNode();
        scr = nm->mkNode(EQUAL, nm->mkNode(k, s, x), t);
      }
      else
      {
        /* s >> x != t
         * with side condition:
         * s != 0 || t != 0  */
        scl = nm->mkNode(OR, s.eqNode(z).notNode(), t.eqNode(z).notNode());
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, s, x), t);
      }
    }
  }
  else
  {
    return Node::null();
  }
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvAshr(bool pol,
                        Kind litk,
                        Kind k,
                        unsigned idx,
                        Node x,
                        Node s,
                        Node t)
{
  Assert(k == BITVECTOR_ASHR);

  NodeManager* nm = NodeManager::currentNM();
  Node scl, scr;
  unsigned w = bv::utils::getSize(s);
  Assert(w == bv::utils::getSize(t));
  Node z = bv::utils::mkZero(w);
  Node n = bv::utils::mkOnes(w);

  if (litk == EQUAL)
  {
    if (idx == 0)
    {
      if (pol)
      {
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

        Node zz = bv::utils::mkZero(w+1);
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

        scl = nm->mkNode(OR, o1, o2, o3);
        scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
      }
      else
      {
        /* x >> s != t
         * no side condition */
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, x, s), t);
      }
    }
    else
    {
      if (pol)
      {
        /* s >> x = t
         * with side condition:
         * (s[w-1:w-1] = 0 && t = 0)
         * ||
         * (s[w-1:w-1] = 1 && t == ~0)
         * ||
         * s = t
         * || 
         * \/ (t[w-1-i:0] = s[w-1:i]
         *     && ((s[w-1:w-1] = 0 && t[w-1:w-i] = 0)
         *         ||
         *         (s[w-1:w-1] = 1 &&  t[w-1:w-i] = ~0)))
         * for 0 < i < w
         * where
         * w = getSize(s) = getSize(t)
         */
        Node msbz = bv::utils::mkExtract(
            s, w-1, w-1).eqNode(bv::utils::mkZero(1));
        Node msbn = bv::utils::mkExtract(
            s, w-1, w-1).eqNode(bv::utils::mkOnes(1));
        NodeBuilder<> nb(nm, OR);
        nb << nm->mkNode(EQUAL, t, s);
        for (unsigned i = 1; i < w; ++i)
        {
          Node ext = bv::utils::mkExtract(t, w-1, w-i);

          Node o1 = nm->mkNode(AND, msbz, ext.eqNode(bv::utils::mkZero(i)));
          Node o2 = nm->mkNode(AND, msbn, ext.eqNode(bv::utils::mkOnes(i)));
          Node o = nm->mkNode(OR, o1, o2);

          Node e = nm->mkNode(EQUAL,
              bv::utils::mkExtract(t, w-1-i, 0), bv::utils::mkExtract(s, w-1, i));

          nb << nm->mkNode(AND, e, o);
        }
        nb << nm->mkNode(AND, msbz, t.eqNode(z));
        nb << nm->mkNode(AND, msbn, t.eqNode(n));
        scl = nb.constructNode();
        scr = nm->mkNode(EQUAL, nm->mkNode(k, s, x), t);
      }
      else
      {
        /* s >> x != t
         * with side condition:
         * (t != 0 || s != 0) && (t != ~0 || s != ~0)  */
        scl = nm->mkNode(AND,
            nm->mkNode(OR, t.eqNode(z).notNode(), s.eqNode(z).notNode()),
            nm->mkNode(OR, t.eqNode(n).notNode(), s.eqNode(n).notNode()));
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, s, x), t);
      }
    }
  }
  else
  {
    return Node::null();
  }
  Node sc = scl.isNull() ? scr : nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

static Node getScBvShl(bool pol,
                       Kind litk,
                       Kind k,
                       unsigned idx,
                       Node x,
                       Node s,
                       Node t)
{
  Assert(k == BITVECTOR_SHL);

  NodeManager* nm = NodeManager::currentNM();
  Node scl, scr;
  unsigned w = bv::utils::getSize(s);
  Assert(w == bv::utils::getSize(t));
  Node z = bv::utils::mkZero(w);

  if (litk == EQUAL)
  {
    if (idx == 0)
    {
      Node ww = bv::utils::mkConst(w, w);

      if (pol)
      {
        /* x << s = t
         * with side condition:
         * (s = 0 || ctz(t) >= s)
         * <->
         * s = 0
         * ||
         * (s < w && ((t o z) >> (z o s))[w-1:0] = z)
         * ||
         * (s >= w && t = 0)
         *
         * where
         * w = getSize(s) = getSize(t) = getSize (z) && z = 0
         */
        Node shr = nm->mkNode(BITVECTOR_LSHR,
            bv::utils::mkConcat(t, z),
            bv::utils::mkConcat(z, s));
        Node ext = bv::utils::mkExtract(shr, w - 1, 0);

        Node o1 = nm->mkNode(EQUAL, s, z);
        Node o2 = nm->mkNode(AND,
            nm->mkNode(BITVECTOR_ULT, s, ww), ext.eqNode(z));
        Node o3 = nm->mkNode(AND,
            nm->mkNode(BITVECTOR_UGE, s, ww), t.eqNode(z));

        scl = nm->mkNode(OR, o1, o2, o3);
        scr = nm->mkNode(EQUAL, nm->mkNode(k, x, s), t);
      }
      else
      {
        /* x << s != t
         * with side condition:
         * t != 0 || s < w
         * with
         * w = getSize(s) = getSize(t)
         */
        scl = nm->mkNode(OR,
            t.eqNode(z).notNode(),
            nm->mkNode(BITVECTOR_ULT, s, ww));
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, x, s), t);
      }
    }
    else
    {
      if (pol)
      {
        /* s << x = t
         * with side condition:
         * t = 0
         * ||
         * s = t
         * || 
         * \/ (t[w-1:i] = s[w-1-i:0] && t[i-1:0] = 0) for 0 < i < w
         * where
         * w = getSize(s) = getSize(t)
         */
        NodeBuilder<> nb(nm, OR);
        nb << nm->mkNode(EQUAL, t, s);
        for (unsigned i = 1; i < w; ++i)
        {
          nb << nm->mkNode(AND,
              nm->mkNode(EQUAL,
                bv::utils::mkExtract(t, w-1, i), bv::utils::mkExtract(s, w-1-i, 0)),
              nm->mkNode(EQUAL,
                bv::utils::mkExtract(t, i-1, 0), bv::utils::mkZero(i)));
        }
        nb << t.eqNode(z);
        scl = nb.constructNode();
        scr = nm->mkNode(EQUAL, nm->mkNode(k, s, x), t);
      }
      else
      {
        /* s << x != t
         * with side condition:
         * s != 0 || t != 0  */
        scl = nm->mkNode(OR, s.eqNode(z).notNode(), t.eqNode(z).notNode());
        scr = nm->mkNode(DISTINCT, nm->mkNode(k, s, x), t);
      }
    }
  }
  else
  {
    return Node::null();
  }
  Node sc = nm->mkNode(IMPLIES, scl, scr);
  Trace("bv-invert") << "Add SC_" << k << "(" << x << "): " << sc << std::endl;
  return sc;
}

Node BvInverter::solveBvLit(Node sv,
                            Node lit,
                            std::vector<unsigned>& path,
                            BvInverterQuery* m)
{
  Assert(!path.empty());

  bool pol = true;
  unsigned index, nchildren;
  NodeManager* nm = NodeManager::currentNM();
  Kind k, litk;

  Assert(!path.empty());
  index = path.back();
  Assert(index < lit.getNumChildren());
  path.pop_back();
  litk = k = lit.getKind();

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
    litk = k = lit.getKind();
  }

  Assert(k == EQUAL
      || k == BITVECTOR_ULT
      || k == BITVECTOR_SLT);

  Node sv_t = lit[index];
  Node t = lit[1-index];

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
    else if (k == BITVECTOR_EXTRACT || k == BITVECTOR_COMP)
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
      if (k == BITVECTOR_PLUS)
      {
        t = nm->mkNode(BITVECTOR_SUB, t, s);
      }
      else if (k == BITVECTOR_SUB)
      {
        t = nm->mkNode(BITVECTOR_PLUS, t, s);
      }
      else if (k == BITVECTOR_XOR)
      {
        t = nm->mkNode(BITVECTOR_XOR, t, s);
      }
      else
      {
        TypeNode solve_tn = sv_t[index].getType();
        Node sc;

        switch (k)
        {
          case BITVECTOR_MULT:
            sc = getScBvMult(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          case BITVECTOR_SHL:
            sc = getScBvShl(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          case BITVECTOR_UREM_TOTAL:
            sc = getScBvUrem(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          case BITVECTOR_UDIV_TOTAL:
            sc = getScBvUdiv(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          case BITVECTOR_AND:
          case BITVECTOR_OR:
            sc = getScBvAndOr(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          case BITVECTOR_LSHR:
            sc = getScBvLshr(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          case BITVECTOR_ASHR:
            sc = getScBvAshr(
                pol, litk, k, index, getSolveVariable(solve_tn), s, t);
            break;

          default:
            Trace("bv-invert") << "bv-invert : Unknown kind " << k
                               << " for bit-vector term " << sv_t << std::endl;
            return Node::null();
        }
        Assert (litk != EQUAL || !sc.isNull());
        /* No specific handling for litk and operator k, generate generic
         * side condition. */
        if (sc.isNull())
        {
          solve_tn = sv_t.getType();
          if (litk == BITVECTOR_ULT)
          {
            sc = getScBvUlt(
                pol, litk, index, getSolveVariable(solve_tn), t);
          }
          else
          {
            Assert (litk == BITVECTOR_SLT);
            sc = getScBvSlt(
                pol, litk, index, getSolveVariable(solve_tn), t);
          }
        }
        /* We generate a choice term (choice x0. SC => x0 <k> s <litk> t) for
         * x <k> s <litk> t. When traversing down, this choice term determines
         * the value for x <k> s = (choice x0. SC => x0 <k> s <litk> t), i.e.,
         * from here on, the propagated literal is a positive equality. */
        litk = EQUAL;
        pol = true;
        /* t = fresh skolem constant */
        t = getInversionNode(sc, solve_tn, m);
      }
    }
    sv_t = sv_t[index];
  }
  Assert(sv_t == sv);
  if (litk == BITVECTOR_ULT)
  {
    TypeNode solve_tn = sv_t.getType();
    Node sc = getScBvUlt(pol, litk, index, getSolveVariable(solve_tn), t);
    t = getInversionNode(sc, solve_tn, m);
  }
  else if (litk == BITVECTOR_SLT)
  {
    TypeNode solve_tn = sv_t.getType();
    Node sc = getScBvSlt(pol, litk, index, getSolveVariable(solve_tn), t);
    t = getInversionNode(sc, solve_tn, m);
  }
  else if (pol == false)
  {
    Assert (litk == EQUAL);
    TypeNode solve_tn = sv_t.getType();
    Node x = getSolveVariable(solve_tn);
    Node sc = nm->mkNode(DISTINCT, x, t);
    Trace("bv-invert") << "Add SC_" << litk << "(" << x << "): " << sc
                       << std::endl;
    t = getInversionNode(sc, solve_tn, m);
  }
  return t;
}

/*---------------------------------------------------------------------------*/

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
