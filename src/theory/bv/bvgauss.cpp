/*********************                                                        */
/*! \file bvgauss.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Gaussian Elimination preprocessing pass.
 **
 ** Simplify a given equation system modulo a (prime) number via Gaussian
 ** Elimination if possible.
 **/

#include "theory/bv/bvgauss.h"

#include <iostream>
#include <stack>
#include <unordered_map>

#include "theory/bv/theory_bv_utils.h"

using namespace CVC4;
using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {

unsigned BVGaussElim::getMinBwExpr(Node expr)
{
  stack<Node> visit;
  unordered_map<Node, unsigned, NodeHashFunction> visited;
  unordered_map<Node, unsigned, NodeHashFunction>::iterator it;

  visit.push(expr);
  while (!visit.empty())
  {
    Node n = visit.top();
    visit.pop();
    it = visited.find(n);
    if (it == visited.end())
    {
      visited[n] = 0;
      visit.push(n);
      for (Node child : n) visit.push(child);
    }
    else if (it->second == 0)
    {
      Kind k = n.getKind();
      switch (k)
      {
        case kind::CONST_BITVECTOR:
        {
          unsigned bwval;
          Integer val = n.getConst<BitVector>().getValue();
          for (bwval = 0; val > 0; val = val.divByPow2(1), ++bwval)
            ;
          visited[n] = bwval;
          break;
        }

        case kind::BITVECTOR_EXTRACT:
        {
          unsigned w = utils::getSize(n);
          visited[n] = w >= visited[n[0]] ? visited[n[0]] : w;
          Assert(visited[n] <= visited[n[0]]);
          break;
        }

        case kind::BITVECTOR_ZERO_EXTEND:
        {
          visited[n] = visited[n[0]];
          break;
        }

        case kind::BITVECTOR_MULT:
        {
          unsigned w = 0;
          for (unsigned i = 0, nc = n.getNumChildren(); i < nc; ++i)
            w += visited[n[i]];
          if (w > utils::getSize(n)) return 0; /* overflow */
          visited[n] = w;
          break;
        }

        case kind::BITVECTOR_CONCAT:
        {
          unsigned w;
          Node zero = utils::mkZero(utils::getSize(n[0]));
          if (n[0] == zero)
          {
            w = visited[n[1]]
                /* add bw of children n[2] to n[n.getNumChildren()-1] */
                + utils::getSize(n) - utils::getSize(n[0])
                - utils::getSize(n[1]);
          }
          else
          {
            w = visited[n[0]]
              /* add bw of children n[1] to n[n.getNumChildren()-1] */
              +  utils::getSize(n) - utils::getSize(n[0]);
          }
          visited[n] = w;
          break;
        }

        case kind::BITVECTOR_UDIV_TOTAL:
        case kind::BITVECTOR_OR:
        case kind::BITVECTOR_NOR:
        case kind::BITVECTOR_XOR:
        case kind::BITVECTOR_XNOR:
        case kind::BITVECTOR_AND:
        case kind::BITVECTOR_NAND:
        case kind::BITVECTOR_SHL:
        case kind::BITVECTOR_LSHR:
        case kind::BITVECTOR_ASHR:
        {
          unsigned wmax = 0;
          for (unsigned i = 0, nc = n.getNumChildren(); i < nc; ++i)
            if (visited[n[i]] > wmax) wmax = visited[n[i]];
          visited[n] = wmax;
          break;
        }

        case kind::BITVECTOR_UREM_TOTAL:
        {
          visited[n] = visited[n[1]];
          break;
        }

        case kind::BITVECTOR_PLUS:
        case kind::BITVECTOR_SUB:
        {
          unsigned w = 0, wmax = visited[n[0]];
          for (unsigned i = 1, nc = n.getNumChildren(); i < nc; ++i)
            if (visited[n[i]] > wmax) wmax = visited[n[i]];
          for (unsigned i = 0, nc = n.getNumChildren(); i < nc; ++i)
            if (visited[n[i]] >= wmax) w += 1;
          w += wmax - 1;
          if (w > utils::getSize(n)) return 0; /* overflow */
          visited[n] = w;
          break;
        }

        case kind::BITVECTOR_NOT:
        case kind::BITVECTOR_NEG:
        {
          visited[n] = visited[n[0]];
          break;
        }

        default:
        {
          visited[n] = utils::getSize(n);
        }
      }
    }
  }
  return visited[expr];
}

BVGaussElim::Result BVGaussElim::gaussElim(Integer prime,
                                           const vector<Integer> &rhs,
                                           const vector<vector<Integer>> &lhs,
                                           vector<Integer> &resrhs,
                                           vector<vector<Integer>> &reslhs)

{
  Assert(prime > 0);
  Assert(lhs.size());
  Assert(lhs.size() == rhs.size());
  Assert(lhs.size() <= lhs[0].size());

  /* special case: zero ring */
  if (prime == 1)
  {
    resrhs = vector<Integer>(rhs.size(), Integer(0));
    reslhs = vector<vector<Integer>>(
        lhs.size(), vector<Integer>(lhs[0].size(), Integer(0)));
    return BVGaussElim::Result::UNIQUE;
  }

  resrhs = vector<Integer>(rhs);
  reslhs = vector<vector<Integer>>(lhs);

  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();

#ifdef CVC4_ASSERTIONS
  for (size_t i = 1; i < nrows; ++i) Assert(lhs[i].size() == ncols);
#endif
  /* (1) if element in pivot column is non-zero and != 1, divide row elements
   *     by element in pivot column modulo prime, i.e., multiply row with
   *     multiplicative inverse of element in pivot column modulo prime
   *
   * (2) subtract pivot row from all rows below pivot row
   *
   * (3) subtract (multiple of) current row from all rows above s.t. all
   *     elements in current pivot column of above rows equal to one
   *
   * Note: we do not normalize the given matrix to values modulo prime
   *       beforehand but on-the-fly. */

  /* pivot = reslhs[pcol][pcol] */
  for (size_t pcol = 0, prow = 0; pcol < ncols && pcol < nrows; ++pcol, ++prow)
  {
    /* reslhs[j][pcol]: element in pivot column */
    for (size_t j = prow; j < nrows; ++j)
    {
#ifdef CVC4_ASSERTIONS
      for (size_t k = 0; k < pcol; ++k) Assert(reslhs[j][k] == 0);
#endif
      /* normalize element in pivot column to modulo prime */
      reslhs[j][pcol] = reslhs[j][pcol].euclidianDivideRemainder(prime);
      /* exchange rows if pivot elem is 0 */
      if (j == prow)
      {
        while (reslhs[j][pcol] == 0)
        {
          for (size_t k = prow + 1; k < nrows; ++k)
          {
            reslhs[k][pcol] = reslhs[k][pcol].euclidianDivideRemainder(prime);
            if (reslhs[k][pcol] != 0)
            {
              std::swap(resrhs[j], resrhs[k]);
              std::swap(reslhs[j], reslhs[k]);
              break;
            }
          }
          if (pcol >= ncols - 1) break;
          if (reslhs[j][pcol] == 0)
          {
            pcol += 1;
            if (reslhs[j][pcol] != 0)
              reslhs[j][pcol] = reslhs[j][pcol].euclidianDivideRemainder(prime);
          }
        }
      }
      /* (1) */
      if (reslhs[j][pcol] != 0)
      {
        if (reslhs[j][pcol] != 1)
        {
          Integer inv = reslhs[j][pcol].modInverse(prime);
          if (inv == -1)
          {
            return BVGaussElim::Result::INVALID; /* not coprime */
          }
          for (size_t k = pcol; k < ncols; ++k)
          {
            reslhs[j][k] = reslhs[j][k].modMultiply(inv, prime);
            if (j <= prow) continue; /** pivot */
            reslhs[j][k] = reslhs[j][k].modAdd(-reslhs[prow][k], prime);
          }
          resrhs[j] = resrhs[j].modMultiply(inv, prime);
          if (j > prow) resrhs[j] = resrhs[j].modAdd(-resrhs[prow], prime);
        }
        /* (2) */
        else if (j != prow)
        {
          for (size_t k = pcol; k < ncols; ++k)
            reslhs[j][k] = reslhs[j][k].modAdd(-reslhs[prow][k], prime);
          resrhs[j] = resrhs[j].modAdd(-resrhs[prow], prime);
        }
      }
    }
    /* (3) */
    for (size_t j = 0; j < prow; ++j)
    {
      Integer mul = reslhs[j][pcol];
      if (mul != 0)
      {
        for (size_t k = pcol; k < ncols; ++k)
          reslhs[j][k] = reslhs[j][k].modAdd(-reslhs[prow][k] * mul, prime);
        resrhs[j] = resrhs[j].modAdd(-resrhs[prow] * mul, prime);
      }
    }
  }

  bool ispart = false;
  for (size_t i = 0; i < nrows; ++i)
  {
    size_t pcol = i;
    while (pcol < ncols && reslhs[i][pcol] == 0) ++pcol;
    if (pcol >= ncols)
    {
      resrhs[i] = resrhs[i].euclidianDivideRemainder(prime);
      if (resrhs[i] != 0) return BVGaussElim::Result::NONE; /* no solution */
      continue;
    }
    for (size_t j = i; j < ncols; ++j)
    {
      if (reslhs[i][j] >= prime || reslhs[i][j] <= -prime)
        reslhs[i][j] = reslhs[i][j].euclidianDivideRemainder(prime);
      if (j > pcol && reslhs[i][j] != 0) ispart = true;
    }
  }
  if (ispart) return BVGaussElim::Result::PARTIAL;

  return BVGaussElim::Result::UNIQUE;
}

static bool is_bv_const(Node n)
{
  for (Kind k = n.getKind(); k != kind::CONST_BITVECTOR; k = n.getKind())
  {
    if (k == kind::BITVECTOR_CONCAT
        && n[0] == utils::mkZero(utils::getSize(n[0])))
    {
      n = n[1];
    }
    else if (k == kind::BITVECTOR_ZERO_EXTEND)
    {
      n = n[0];
    }
    else
    {
      return false;
    }
  }
  return n.getKind() == kind::CONST_BITVECTOR;
}

static Integer get_bv_const(Node n)
{
  Assert(is_bv_const(n));

  for (Kind k = n.getKind(); k != kind::CONST_BITVECTOR; k = n.getKind())
  {
    if (k == kind::BITVECTOR_CONCAT)
    {
      Assert(n[0] == utils::mkZero(utils::getSize(n[0])));
      n = n[1];
    }
    else
    {
      Assert(k == kind::BITVECTOR_ZERO_EXTEND);
      n = n[0];
    }
  }
  Assert(n.getKind() == kind::CONST_BITVECTOR);
  return n.getConst<BitVector>().getValue();
}

BVGaussElim::Result BVGaussElim::gaussElimRewriteForUrem(
    vector<Node> &equations, unordered_map<Node, Node, NodeHashFunction> &res)
{
  Node prime;
  Integer iprime;
  unordered_map<Node, vector<Integer>, NodeHashFunction> vars;
  size_t neqs = equations.size();
  vector<Integer> resrhs, rhs;
  vector<vector<Integer>> reslhs,
      lhs = vector<vector<Integer>>(neqs, vector<Integer>());

  res = unordered_map<Node, Node, NodeHashFunction>();

  for (size_t i = 0; i < neqs; ++i)
  {
    Node eq = equations[i];
    Assert(eq.getKind() == kind::EQUAL);
    Node urem, eqrhs;

    if (eq[0].getKind() == kind::BITVECTOR_UREM)
    {
      urem = eq[0];
      Assert(is_bv_const(eq[1]));
      eqrhs = eq[1];
    }
    else
    {
      Assert(eq[1].getKind() == kind::BITVECTOR_UREM);
      urem = eq[1];
      Assert(is_bv_const(eq[0]));
      eqrhs = eq[0];
    }
    if (getMinBwExpr(urem[0]) == 0)
    {
      Trace("bv-gauss-elim")
          << "Minimum required bit-width exceeds given bit-width, "
             "will not apply Gaussian Elimination."
          << endl;
      return BVGaussElim::Result::INVALID;
    }
    rhs.push_back(get_bv_const(eqrhs));

    Assert(is_bv_const(urem[1]));
    Assert(i == 0 || get_bv_const(urem[1]) == iprime);
    if (i == 0)
    {
      prime = urem[1];
      iprime = get_bv_const(prime);
    }

    unordered_map<Node, Integer, NodeHashFunction> tmp;
    bool isvalid = true;
    stack<Node> stack;
    stack.push(urem[0]);
    while (!stack.empty())
    {
      Node n = stack.top();
      stack.pop();
      Kind k = n.getKind();
      if (k == kind::BITVECTOR_PLUS)
      {
        for (Node child : n) stack.push(child);
      }
      else if (k == kind::BITVECTOR_MULT)
      {
        unsigned nchild = n.getNumChildren();
        Node n0, n1;

        if (nchild == 2)
        {
          n0 = n[0];
          n1 = n[1];
        }
        else
        {
          NodeBuilder<> nb(NodeManager::currentNM(), k);

          for (size_t j = 0; j < nchild; ++j)
          {
            if (n0 == Node::null() && is_bv_const(n[j]))
            {
              n0 = n[j];
            }
            else
            {
              nb << n[j];
            }
          }
          if (n0 == Node::null())
          {
            isvalid = false;
            break;
          }
          n1 = nb.constructNode();
        }

        if (!isvalid)
        {
          tmp[n] += Integer(1);
        }
        else
        {
          if (is_bv_const(n0) && !is_bv_const(n1))
          {
            tmp[n1] += get_bv_const(n0);
          }
          else if (!is_bv_const(n0) && is_bv_const(n1))
          {
            tmp[n0] += get_bv_const(n1);
          }
          else
          {
            tmp[n] += Integer(1);
          }
        }
      }
      else
      {
        tmp[n] += Integer(1);
      }
    }

    /* Note: "var" is not necessarily a VARIABLE but can be an arbitrary expr */

    for (auto p : tmp)
    {
      Node var = p.first;
      Integer val = p.second;
      if (i > 0 && vars.find(var) == vars.end())
      {
        for (size_t j = 0; j < i; ++j) vars[var].push_back(Integer(0));
      }
      vars[var].push_back(val);
    }

    for (auto p : vars)
    {
      if (tmp.find(p.first) == tmp.end())
      {
        vars[p.first].push_back(Integer(0));
      }
    }
  }

  size_t nvars = vars.size();
  Assert(nvars);
  size_t nrows = vars.begin()->second.size();
#ifdef CVC4_ASSERTIONS
  for (auto p : vars) Assert(p.second.size() == nrows);
#endif

  if (nrows < 1)
  {
    return BVGaussElim::Result::INVALID;
  }

  for (size_t i = 0; i < nrows; ++i)
    for (auto p : vars) lhs[i].push_back(p.second[i]);

#ifdef CVC4_ASSERTIONS
  for (size_t i = 0; i < nrows; ++i) Assert(lhs[i].size() == nvars);
  Assert(lhs.size() == rhs.size());
#endif

  if (lhs.size() > lhs[0].size())
  {
    return BVGaussElim::Result::INVALID;
  }

  Trace("bv-gauss-elim") << "Applying Gaussian Elimination..." << endl;
  Result ret = gaussElim(iprime, rhs, lhs, resrhs, reslhs);

  if (ret != BVGaussElim::Result::NONE && ret != BVGaussElim::Result::INVALID)
  {
    vector<Node> vvars;
    for (auto p : vars) vvars.push_back(p.first);
    Assert(nvars == vvars.size());
    Assert(lhs[0].size() == reslhs[0].size());
    Assert(nrows == lhs.size());
    Assert(lhs.size() == reslhs.size());
    Assert(nrows == rhs.size());
    Assert(rhs.size() == resrhs.size());
    NodeManager *nm = NodeManager::currentNM();
    if (ret == BVGaussElim::Result::UNIQUE)
    {
      for (size_t i = 0; i < nvars; ++i)
      {
        res[vvars[i]] = nm->mkConst<BitVector>(
            BitVector(utils::getSize(vvars[i]), resrhs[i]));
      }
    }
    else
    {
      Assert(ret == BVGaussElim::Result::PARTIAL);

      for (size_t pcol = 0, prow = 0; pcol < nvars && pcol < nrows;
           ++pcol, ++prow)
      {
        Assert(reslhs[prow][pcol] == 0 || reslhs[prow][pcol] == 1);
        while (pcol < nvars && reslhs[prow][pcol] == 0) pcol += 1;
        if (pcol >= nvars)
        {
          Assert(resrhs[prow] == 0);
          break;
        }
        if (reslhs[prow][pcol] == 0)
        {
          Assert(resrhs[prow] == 0);
          continue;
        }
        Assert(reslhs[prow][pcol] == 1);
        vector<Node> stack;
        while (reslhs[prow][pcol] == 0) pcol += 1;
        for (size_t i = pcol + 1; i < nvars; ++i)
        {
          if (reslhs[prow][i] == 0) continue;
          /* Normalize (no negative numbers, hence no subtraction)
           * e.g., x = 4 - 2y  --> x = 4 + 9y (modulo 11) */
          Integer m = iprime - reslhs[prow][i];
          Node bv =
              nm->mkConst<BitVector>(BitVector(utils::getSize(vvars[i]), m));
          Node mult = nm->mkNode(kind::BITVECTOR_MULT, vvars[i], bv);
          stack.push_back(mult);
        }

        if (stack.empty())
        {
          res[vvars[pcol]] = nm->mkConst<BitVector>(
              BitVector(utils::getSize(vvars[pcol]), resrhs[prow]));
        }
        else
        {
          Node tmp = stack.back();
          stack.pop_back();
          if (resrhs[prow] != 0)
          {
            tmp = nm->mkNode(kind::BITVECTOR_PLUS,
                             nm->mkConst<BitVector>(BitVector(
                                 utils::getSize(vvars[pcol]), resrhs[prow])),
                             tmp);
          }
          while (!stack.empty())
          {
            tmp = nm->mkNode(kind::BITVECTOR_PLUS, tmp, stack.back());
            stack.pop_back();
          }
          if (is_bv_const(tmp))
          {
            res[vvars[pcol]] = tmp;
          }
          else
          {
            res[vvars[pcol]] = nm->mkNode(kind::BITVECTOR_UREM, tmp, prime);
          }
        }
      }
    }
  }
  return ret;
}

void BVGaussElim::gaussElimRewrite(std::vector<Node> &assertionsToPreprocess)
{
  vector<Node> assertions;
  unordered_map<Node, vector<Node>, NodeHashFunction> equations;
  vector<Integer> resrhs;
  vector<vector<Integer>> reslhs;

  for (Node aa : assertionsToPreprocess)
    assertions.push_back(aa);

  while (!assertions.empty())
  {
    Node a = assertions.back();
    assertions.pop_back();
    CVC4::Kind k = a.getKind();

    if (k == kind::AND)
    {
      for (Node aa : a) assertions.push_back(aa);
    }
    else if (k == kind::EQUAL)
    {
      Node urem;

      if (is_bv_const(a[0]) && a[1].getKind() == kind::BITVECTOR_UREM)
        urem = a[1];
      else if (is_bv_const(a[1]) && a[0].getKind() == kind::BITVECTOR_UREM)
        urem = a[0];
      else
        continue;

      if (urem[0].getKind() == kind::BITVECTOR_PLUS && is_bv_const(urem[1]))
      {
        equations[urem[1]].push_back(a);
      }
    }
  }

  unordered_map<Node, Node, NodeHashFunction> subst;
  unsigned size = assertionsToPreprocess.size();

  for (auto eq : equations)
  {
    if (eq.second.size() <= 1) continue;
    unordered_map<Node, Node, NodeHashFunction> res;
    BVGaussElim::Result ret = gaussElimRewriteForUrem(eq.second, res);
    Trace("bv-gauss-elim") << "result: "
                           << (ret == BVGaussElim::Result::INVALID
                                   ? "INVALID"
                                   : (ret == BVGaussElim::Result::UNIQUE
                                          ? "UNIQUE"
                                          : (ret == BVGaussElim::Result::PARTIAL
                                                 ? "PARTIAL"
                                                 : "NONE")))
                           << endl;
    if (ret != BVGaussElim::Result::INVALID)
    {
      NodeManager *nm = NodeManager::currentNM();
      if (ret == BVGaussElim::Result::NONE)
      {
        assertionsToPreprocess.clear();
        assertionsToPreprocess.push_back(nm->mkConst<bool>(false));
      }
      else
      {
        for (Node e : eq.second) subst[e] = nm->mkConst<bool>(true);
        /* add resulting constraints */
        for (auto p : res)
        {
          Node a = nm->mkNode(kind::EQUAL, p.first, p.second);
          Trace("bv-gauss-elim") << "added assertion: " << a << endl;
          assertionsToPreprocess.push_back(a);
        }
      }
    }
  }

  if (!subst.empty())
  {
    /* delete (= substitute with true) obsolete assertions */
    for (unsigned i = 0; i < size; ++i)
    {
      assertionsToPreprocess[i] =
          assertionsToPreprocess[i].substitute(subst.begin(), subst.end());
    }
  }
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
