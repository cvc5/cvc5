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

#include "theory/quantifiers/term_database.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory::quantifiers;

Node BvInverter::getSolveVariable(TypeNode tn) {
  std::map<TypeNode, Node>::iterator its = d_solve_var.find(tn);
  if (its == d_solve_var.end()) {
    std::stringstream ss;
    if (tn.isFunction()) {
      Assert(tn.getNumChildren() == 2);
      Assert(tn[0].isBoolean());
      ss << "slv_f";
    } else {
      ss << "slv";
    }
    Node k = NodeManager::currentNM()->mkSkolem(ss.str(), tn);
    // marked as a virtual term (it is eligible for instantiation)
    VirtualTermSkolemAttribute vtsa;
    k.setAttribute(vtsa, true);
    d_solve_var[tn] = k;
    return k;
  } else {
    return its->second;
  }
}

Node BvInverter::getInversionSkolemFor(Node cond, TypeNode tn) {
  // condition should be rewritten
  Assert(Rewriter::rewrite(cond) == cond);
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it =
      d_inversion_skolem_cache.find(cond);
  if (it == d_inversion_skolem_cache.end()) {
    Node skv;
    if (cond.getKind() == EQUAL) {
      // optimization : if condition is ( x = v ) should just return v and not
      // introduce a Skolem this can happen when we ask for the multiplicative
      // inversion with bv1
      Node x = getSolveVariable(tn);
      for (unsigned i = 0; i < 2; i++) {
        if (cond[i] == x) {
          skv = cond[1 - i];
          Trace("cegqi-bv-skvinv")
              << "SKVINV : " << skv << " is trivially associated with conditon "
              << cond << std::endl;
          break;
        }
      }
    }
    if (skv.isNull()) {
      // TODO : compute the value if the condition is deterministic, e.g. calc
      // multiplicative inverse of 2 constants
      skv = NodeManager::currentNM()->mkSkolem("skvinv", tn,
                                               "created for BvInverter");
      Trace("cegqi-bv-skvinv")
          << "SKVINV : " << skv << " is the skolem associated with conditon "
          << cond << std::endl;
      // marked as a virtual term (it is eligible for instantiation)
      VirtualTermSkolemAttribute vtsa;
      skv.setAttribute(vtsa, true);
    }
    d_inversion_skolem_cache[cond] = skv;
    return skv;
  } else {
    Assert(it->second.getType() == tn);
    return it->second;
  }
}

Node BvInverter::getInversionSkolemFunctionFor(TypeNode tn) {
  NodeManager* nm = NodeManager::currentNM();
  // function maps conditions to skolems
  TypeNode ftn = nm->mkFunctionType(nm->booleanType(), tn);
  return getSolveVariable(ftn);
}

Node BvInverter::getInversionNode(Node cond, TypeNode tn) {
  // condition should be rewritten
  Node new_cond = Rewriter::rewrite(cond);
  if (new_cond != cond) {
    Trace("bv-invert-debug") << "Condition " << cond << " was rewritten to "
                             << new_cond << std::endl;
  }
  Node f = getInversionSkolemFunctionFor(tn);
  return NodeManager::currentNM()->mkNode(kind::APPLY_UF, f, new_cond);
}

bool BvInverter::isInvertible(Kind k) {
  // TODO : make this precise (this should correspond to all kinds that we
  // handle in solve_bv_lit/solve_bv_constraint)
  return k != APPLY_UF;
}

Node BvInverter::getPathToPv(
    Node lit, Node pv, Node sv, std::vector<unsigned>& path,
    std::unordered_set<TNode, TNodeHashFunction>& visited) {
  if (visited.find(lit) == visited.end()) {
    visited.insert(lit);
    if (lit == pv) {
      return sv;
    } else {
      // only recurse if the kind is invertible
      // this allows us to avoid paths that go through skolem functions
      if (isInvertible(lit.getKind())) {
        unsigned rmod = 0;  // TODO : randomize?
        for (unsigned i = 0; i < lit.getNumChildren(); i++) {
          unsigned ii = (i + rmod) % lit.getNumChildren();
          Node litc = getPathToPv(lit[ii], pv, sv, path, visited);
          if (!litc.isNull()) {
            // path is outermost term index last
            path.push_back(ii);
            std::vector<Node> children;
            if (lit.getMetaKind() == kind::metakind::PARAMETERIZED) {
              children.push_back(lit.getOperator());
            }
            for (unsigned j = 0; j < lit.getNumChildren(); j++) {
              children.push_back(j == ii ? litc : lit[j]);
            }
            return NodeManager::currentNM()->mkNode(lit.getKind(), children);
          }
        }
      }
    }
  }
  return Node::null();
}

Node BvInverter::eliminateSkolemFunctions(TNode n,
                                          std::vector<Node>& side_conditions) {
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;

  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();

    std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it =
        visited.find(cur);

    if (it == visited.end()) {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
        visit.push_back(cur[i]);
    } else if (it->second.isNull()) {
      Trace("bv-invert-debug")
          << "eliminateSkolemFunctions from " << cur << "..." << std::endl;

      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        it = visited.find(cur[i]);
        Assert(it != visited.end());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (childChanged) {
        ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
      }
      // now, check if it is a skolem function
      if (ret.getKind() == APPLY_UF) {
        Node op = ret.getOperator();
        TypeNode tnp = op.getType();
        // is this a skolem function?
        std::map<TypeNode, Node>::iterator its = d_solve_var.find(tnp);
        if (its != d_solve_var.end() && its->second == op) {
          Assert(ret.getNumChildren() == 1);
          Assert(ret[0].getType().isBoolean());

          Node cond = ret[0];
          // must rewrite now to ensure we lookup the correct skolem
          cond = Rewriter::rewrite(cond);

          // if so, we replace by the (finalized) skolem variable
          // Notice that since we are post-rewriting, skolem functions are
          // already eliminated from cond
          ret = getInversionSkolemFor(cond, ret.getType());

          // also must add (substituted) side condition to vector
          // substitute ( solve variable -> inversion skolem )
          TNode solve_var = getSolveVariable(ret.getType());
          TNode tret = ret;
          cond = cond.substitute(solve_var, tret);
          if (std::find(side_conditions.begin(), side_conditions.end(), cond) ==
              side_conditions.end()) {
            side_conditions.push_back(cond);
          }
        }
      }
      Trace("bv-invert-debug") << "eliminateSkolemFunctions from " << cur
                               << " returned " << ret << std::endl;
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  return visited[n];
}

Node BvInverter::getPathToPv(Node lit, Node pv, Node sv, Node pvs,
                             std::vector<unsigned>& path) {
  std::unordered_set<TNode, TNodeHashFunction> visited;
  Node slit = getPathToPv(lit, pv, sv, path, visited);
  // if we are able to find a (invertible) path to pv
  if (!slit.isNull()) {
    // substitute pvs for the other occurrences of pv
    TNode tpv = pv;
    TNode tpvs = pvs;
    slit = slit.substitute(tpv, tpvs);
  }
  return slit;
}

Node BvInverter::solve_bv_constraint(Node sv, Node sv_t, Node t, Kind rk,
                                     bool pol, std::vector<unsigned>& path,
                                     BvInverterModelQuery* m,
                                     BvInverterStatus& status) {
  NodeManager* nm = NodeManager::currentNM();
  while (!path.empty()) {
    unsigned index = path.back();
    Assert(sv_t.getNumChildren() <= 2);
    Assert(index < sv_t.getNumChildren());
    path.pop_back();
    Kind k = sv_t.getKind();
    // inversions
    if (k == BITVECTOR_PLUS) {
      t = nm->mkNode(BITVECTOR_SUB, t, sv_t[1 - index]);
    } else if (k == BITVECTOR_SUB) {
      t = nm->mkNode(BITVECTOR_PLUS, t, sv_t[1 - index]);
    } else if (k == BITVECTOR_MULT) {
      // t = skv (fresh skolem constant)
      TypeNode solve_tn = sv_t[index].getType();
      Node x = getSolveVariable(solve_tn);
      // with side condition:
      // ctz(t) >= ctz(s) <-> x * s = t
      // where
      // ctz(t) >= ctz(s) -> (t & -t) >= (s & -s)
      Node s = sv_t[1 - index];
      // left hand side of side condition
      Node scl = nm->mkNode(
          BITVECTOR_UGE,
          nm->mkNode(BITVECTOR_AND, t, nm->mkNode(BITVECTOR_NEG, t)),
          nm->mkNode(BITVECTOR_AND, s, nm->mkNode(BITVECTOR_NEG, s)));
      // right hand side of side condition
      Node scr = nm->mkNode(EQUAL, nm->mkNode(BITVECTOR_MULT, x, s), t);
      // overall side condition
      Node sc = nm->mkNode(IMPLIES, scl, scr);
      // add side condition
      status.d_conds.push_back(sc);

      // get the skolem node for this side condition
      Node skv = getInversionNode(sc, solve_tn);
      // now solving with the skolem node as the RHS
      t = skv;

    } else if (k == BITVECTOR_NEG || k == BITVECTOR_NOT) {
      t = NodeManager::currentNM()->mkNode(k, t);
      //}else if( k==BITVECTOR_AND || k==BITVECTOR_OR ){
      // TODO
      //}else if( k==BITVECTOR_CONCAT ){
      // TODO
      //}else if( k==BITVECTOR_SHL || k==BITVECTOR_LSHR ){
      // TODO
      //}else if( k==BITVECTOR_ASHR ){
      // TODO
    } else {
      Trace("bv-invert") << "bv-invert : Unknown kind for bit-vector term " << k
                         << ", from " << sv_t << std::endl;
      return Node::null();
    }
    sv_t = sv_t[index];
  }
  Assert(sv_t == sv);
  // finalize based on the kind of constraint
  // TODO
  if (rk == EQUAL) {
    return t;
  } else {
    Trace("bv-invert")
        << "bv-invert : Unknown relation kind for bit-vector literal " << rk
        << std::endl;
    return t;
  }
}

Node BvInverter::solve_bv_lit(Node sv, Node lit, bool pol,
                              std::vector<unsigned>& path,
                              BvInverterModelQuery* m,
                              BvInverterStatus& status) {
  Assert(!path.empty());
  unsigned index = path.back();
  Assert(index < lit.getNumChildren());
  path.pop_back();
  Kind k = lit.getKind();
  if (k == NOT) {
    Assert(index == 0);
    return solve_bv_lit(sv, lit[index], !pol, path, m, status);
  } else if (k == EQUAL) {
    return solve_bv_constraint(sv, lit[index], lit[1 - index], k, pol, path, m,
                               status);
  } else if (k == BITVECTOR_ULT || k == BITVECTOR_ULE || k == BITVECTOR_SLT ||
             k == BITVECTOR_SLE) {
    if (!pol) {
      if (k == BITVECTOR_ULT) {
        k = index == 1 ? BITVECTOR_ULE : BITVECTOR_UGE;
      } else if (k == BITVECTOR_ULE) {
        k = index == 1 ? BITVECTOR_ULT : BITVECTOR_UGT;
      } else if (k == BITVECTOR_SLT) {
        k = index == 1 ? BITVECTOR_SLE : BITVECTOR_SGE;
      } else {
        Assert(k == BITVECTOR_SLE);
        k = index == 1 ? BITVECTOR_SLT : BITVECTOR_SGT;
      }
    } else if (index == 1) {
      if (k == BITVECTOR_ULT) {
        k = BITVECTOR_UGT;
      } else if (k == BITVECTOR_ULE) {
        k = BITVECTOR_UGE;
      } else if (k == BITVECTOR_SLT) {
        k = BITVECTOR_SGT;
      } else {
        Assert(k == BITVECTOR_SLE);
        k = BITVECTOR_SGE;
      }
    }
    return solve_bv_constraint(sv, lit[index], lit[1 - index], k, true, path, m,
                               status);
  } else {
    Trace("bv-invert") << "bv-invert : Unknown kind for bit-vector literal "
                       << lit << std::endl;
  }
  return Node::null();
}
