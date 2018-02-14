/*********************                                                        */
/*! \file bvgauss.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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

#include <unordered_map>

#include "theory/rewriter.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"

using namespace CVC4;

namespace CVC4 {
namespace theory {
namespace bv {

static bool is_bv_const(Node n)
{
  if (n.isConst()) { return true; }
  return Rewriter::rewrite(n).getKind() == kind::CONST_BITVECTOR;
}

static Node get_bv_const(Node n)
{
  Assert(is_bv_const(n));
  return Rewriter::rewrite(n);
}

static Integer get_bv_const_value(Node n)
{
  Assert(is_bv_const(n));
  return get_bv_const(n).getConst<BitVector>().getValue();
}

/* Note: getMinBwExpr assumes that 'expr' is rewritten.
 *
 * If not, all operators that are removed via rewriting (e.g., ror, rol, ...)
 * will be handled via the default case, which is not incorrect but also not
 * necessarily the minimum. */
unsigned BVGaussElim::getMinBwExpr(Node expr)
{
  std::vector<Node> visit;
  /* Maps visited nodes to the determined minimum bit-width required. */
  std::unordered_map<Node, unsigned, NodeHashFunction> visited;
  std::unordered_map<Node, unsigned, NodeHashFunction>::iterator it;

  visit.push_back(expr);
  while (!visit.empty())
  {
    Node n = visit.back();
    visit.pop_back();
    it = visited.find(n);
    if (it == visited.end())
    {
      if (is_bv_const(n))
      {
        /* Rewrite const expr, overflows in consts are irrelevant. */
        visited[n] = get_bv_const(n).getConst<BitVector>().getValue().length();
      }
      else
      {
        visited[n] = 0;
        visit.push_back(n);
        for (const Node &nn : n) { visit.push_back(nn); }
      }
    }
    else if (it->second == 0)
    {
      Kind k = n.getKind();
      Assert(k != kind::CONST_BITVECTOR);
      Assert(!is_bv_const(n));
      switch (k)
      {
        case kind::BITVECTOR_EXTRACT:
        {
          const unsigned size = utils::getSize(n);
          const unsigned low = utils::getExtractLow(n);
          const unsigned child_min_width = visited[n[0]];
          visited[n] = std::min(
              size, child_min_width >= low ? child_min_width - low : 0u);
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
          Integer maxval = Integer(1);
          for (const Node& nn : n)
          {
            if (is_bv_const(nn))
            {
              maxval *= get_bv_const_value(nn);
            }
            else
            {
              maxval *= BitVector::mkOnes(visited[nn]).getValue();
            }
          }
          unsigned w = maxval.length();
          if (w > utils::getSize(n)) { return 0; } /* overflow */
          visited[n] = w;
          break;
        }

        case kind::BITVECTOR_CONCAT:
        {
          unsigned i, wnz, nc;
          for (i = 0, wnz = 0, nc = n.getNumChildren() - 1; i < nc; ++i)
          {
            unsigned wni = utils::getSize(n[i]);
            if (n[i] != utils::mkZero(wni)) { break; }
            /* sum of all bit-widths of leading zero concats */
            wnz += wni;
          }
          /* Do not consider leading zero concats, i.e.,
           * min bw of current concat is determined as
           *   min bw of first non-zero term
           *   plus actual bw of all subsequent terms */
          visited[n] = utils::getSize(n)
                       + visited[n[i]] - utils::getSize(n[i])
                       - wnz;
          break;
        }

        case kind::BITVECTOR_UREM_TOTAL:
        case kind::BITVECTOR_LSHR:
        case kind::BITVECTOR_ASHR:
        {
          visited[n] = visited[n[0]];
          break;
        }

        case kind::BITVECTOR_OR:
        case kind::BITVECTOR_NOR:
        case kind::BITVECTOR_XOR:
        case kind::BITVECTOR_XNOR:
        case kind::BITVECTOR_AND:
        case kind::BITVECTOR_NAND:
        {
          unsigned wmax = 0;
          for (const Node &nn : n)
          {
            if (visited[nn] > wmax)
            {
              wmax = visited[nn];
            }
          }
          visited[n] = wmax;
          break;
        }

        case kind::BITVECTOR_PLUS:
        {
          Integer maxval = Integer(0);
          for (const Node& nn : n)
          {
            if (is_bv_const(nn))
            {
              maxval += get_bv_const_value(nn);
            }
            else
            {
              maxval += BitVector::mkOnes(visited[nn]).getValue();
            }
          }
          unsigned w = maxval.length();
          if (w > utils::getSize(n)) { return 0; } /* overflow */
          visited[n] = w;
          break;
        }

        default:
        {
          /* BITVECTOR_UDIV_TOTAL (since x / 0 = -1)
           * BITVECTOR_NOT
           * BITVECTOR_NEG
           * BITVECTOR_SHL */
          visited[n] = utils::getSize(n);
        }
      }
    }
  }
  Assert(visited.find(expr) != visited.end());
  return visited[expr];
}

BVGaussElim::Result BVGaussElim::gaussElim(
    Integer prime,
    std::vector<Integer>& rhs,
    std::vector<std::vector<Integer>>& lhs)
{
  Assert(prime > 0);
  Assert(lhs.size());
  Assert(lhs.size() == rhs.size());
  Assert(lhs.size() <= lhs[0].size());

  /* special case: zero ring */
  if (prime == 1)
  {
    rhs = std::vector<Integer>(rhs.size(), Integer(0));
    lhs = std::vector<std::vector<Integer>>(
        lhs.size(), std::vector<Integer>(lhs[0].size(), Integer(0)));
    return BVGaussElim::Result::UNIQUE;
  }

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
   *     elements in current pivot column above current row become equal to one
   *
   * Note: we do not normalize the given matrix to values modulo prime
   *       beforehand but on-the-fly. */

  /* pivot = lhs[pcol][pcol] */
  for (size_t pcol = 0, prow = 0; pcol < ncols && prow < nrows; ++pcol, ++prow)
  {
    /* lhs[j][pcol]: element in pivot column */
    for (size_t j = prow; j < nrows; ++j)
    {
#ifdef CVC4_ASSERTIONS
      for (size_t k = 0; k < pcol; ++k) { Assert(lhs[j][k] == 0); }
#endif
      /* normalize element in pivot column to modulo prime */
      lhs[j][pcol] = lhs[j][pcol].euclidianDivideRemainder(prime);
      /* exchange rows if pivot elem is 0 */
      if (j == prow)
      {
        while (lhs[j][pcol] == 0)
        {
          for (size_t k = prow + 1; k < nrows; ++k)
          {
            lhs[k][pcol] = lhs[k][pcol].euclidianDivideRemainder(prime);
            if (lhs[k][pcol] != 0)
            {
              std::swap(rhs[j], rhs[k]);
              std::swap(lhs[j], lhs[k]);
              break;
            }
          }
          if (pcol >= ncols - 1) break;
          if (lhs[j][pcol] == 0)
          {
            pcol += 1;
            if (lhs[j][pcol] != 0)
              lhs[j][pcol] = lhs[j][pcol].euclidianDivideRemainder(prime);
          }
        }
      }

      if (lhs[j][pcol] != 0)
      {
        /* (1) */
        if (lhs[j][pcol] != 1)
        {
          Integer inv = lhs[j][pcol].modInverse(prime);
          if (inv == -1)
          {
            return BVGaussElim::Result::INVALID; /* not coprime */
          }
          for (size_t k = pcol; k < ncols; ++k)
          {
            lhs[j][k] = lhs[j][k].modMultiply(inv, prime);
            if (j <= prow) continue; /* pivot */
            lhs[j][k] = lhs[j][k].modAdd(-lhs[prow][k], prime);
          }
          rhs[j] = rhs[j].modMultiply(inv, prime);
          if (j > prow) { rhs[j] = rhs[j].modAdd(-rhs[prow], prime); }
        }
        /* (2) */
        else if (j != prow)
        {
          for (size_t k = pcol; k < ncols; ++k)
          {
            lhs[j][k] = lhs[j][k].modAdd(-lhs[prow][k], prime);
          }
          rhs[j] = rhs[j].modAdd(-rhs[prow], prime);
        }
      }
    }
    /* (3) */
    for (size_t j = 0; j < prow; ++j)
    {
      Integer mul = lhs[j][pcol];
      if (mul != 0)
      {
        for (size_t k = pcol; k < ncols; ++k)
        {
          lhs[j][k] = lhs[j][k].modAdd(-lhs[prow][k] * mul, prime);
        }
        rhs[j] = rhs[j].modAdd(-rhs[prow] * mul, prime);
      }
    }
  }

  bool ispart = false;
  for (size_t i = 0; i < nrows; ++i)
  {
    size_t pcol = i;
    while (pcol < ncols && lhs[i][pcol] == 0) ++pcol;
    if (pcol >= ncols)
    {
      rhs[i] = rhs[i].euclidianDivideRemainder(prime);
      if (rhs[i] != 0)
      {
        /* no solution */
        return BVGaussElim::Result::NONE;
      }
      continue;
    }
    for (size_t j = i; j < ncols; ++j)
    {
      if (lhs[i][j] >= prime || lhs[i][j] <= -prime)
      {
        lhs[i][j] = lhs[i][j].euclidianDivideRemainder(prime);
      }
      if (j > pcol && lhs[i][j] != 0)
      {
        ispart = true;
      }
    }
  }

  if (ispart) { return BVGaussElim::Result::PARTIAL; }

  return BVGaussElim::Result::UNIQUE;
}

BVGaussElim::Result BVGaussElim::gaussElimRewriteForUrem(
    const std::vector<Node>& equations,
    std::unordered_map<Node, Node, NodeHashFunction>& res)
{
  Assert(res.empty());

  Node prime;
  Integer iprime;
  std::unordered_map<Node, std::vector<Integer>, NodeHashFunction> vars;
  size_t neqs = equations.size();
  std::vector<Integer> rhs;
  std::vector<std::vector<Integer>> lhs =
      std::vector<std::vector<Integer>>(neqs, std::vector<Integer>());

  res = std::unordered_map<Node, Node, NodeHashFunction>();

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
    if (getMinBwExpr(Rewriter::rewrite(urem[0])) == 0)
    {
      Trace("bv-gauss-elim")
          << "Minimum required bit-width exceeds given bit-width, "
             "will not apply Gaussian Elimination."
          << std::endl;
      return BVGaussElim::Result::INVALID;
    }
    rhs.push_back(get_bv_const_value(eqrhs));

    Assert(is_bv_const(urem[1]));
    Assert(i == 0 || get_bv_const_value(urem[1]) == iprime);
    if (i == 0)
    {
      prime = urem[1];
      iprime = get_bv_const_value(prime);
    }

    std::unordered_map<Node, Integer, NodeHashFunction> tmp;
    std::vector<Node> stack;
    stack.push_back(urem[0]);
    while (!stack.empty())
    {
      Node n = stack.back();
      stack.pop_back();

      /* Subtract from rhs if const */
      if (is_bv_const(n))
      {
        Integer val = get_bv_const_value(n);
        if (val > 0) rhs.back() -= val;
        continue;
      }

      /* Split into matrix columns */
      Kind k = n.getKind();
      if (k == kind::BITVECTOR_PLUS)
      {
        for (const Node& nn : n) { stack.push_back(nn); }
      }
      else if (k == kind::BITVECTOR_MULT)
      {
        Node n0, n1;
        /* Flatten mult expression. */
        n = RewriteRule<FlattenAssocCommut>::run<true>(n);
        /* Split operands into consts and non-consts */
        NodeBuilder<> nb_consts(NodeManager::currentNM(), k);
        NodeBuilder<> nb_nonconsts(NodeManager::currentNM(), k);
        for (const Node& nn : n)
        {
          Node nnrw = Rewriter::rewrite(nn);
          if (is_bv_const(nnrw))
          {
            nb_consts << nnrw;
          }
          else
          {
            nb_nonconsts << nnrw;
          }
        }
        Assert(nb_nonconsts.getNumChildren() > 0);
        /* n0 is const */
        unsigned nc = nb_consts.getNumChildren();
        if (nc > 1)
        {
          n0 = Rewriter::rewrite(nb_consts.constructNode());
        }
        else if (nc == 1)
        {
          n0 = nb_consts[0];
        }
        else
        {
          n0 = utils::mkOne(utils::getSize(n));
        }
        /* n1 is a mult with non-const operands */
        if (nb_nonconsts.getNumChildren() > 1)
        {
          n1 = Rewriter::rewrite(nb_nonconsts.constructNode());
        }
        else
        {
          n1 = nb_nonconsts[0];
        }
        Assert(is_bv_const(n0));
        Assert(!is_bv_const(n1));
        tmp[n1] += get_bv_const_value(n0);
      }
      else
      {
        tmp[n] += Integer(1);
      }
    }

    /* Note: "var" is not necessarily a VARIABLE but can be an arbitrary expr */

    for (const auto& p : tmp)
    {
      Node var = p.first;
      Integer val = p.second;
      if (i > 0 && vars.find(var) == vars.end())
      {
        /* Add column and fill column elements of rows above with 0. */
        vars[var].insert(vars[var].end(), i, Integer(0));
      }
      vars[var].push_back(val);
    }

    for (const auto& p : vars)
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
  for (const auto& p : vars) { Assert(p.second.size() == nrows); }
#endif

  if (nrows < 1)
  {
    return BVGaussElim::Result::INVALID;
  }

  for (size_t i = 0; i < nrows; ++i)
  {
    for (const auto& p : vars)
    {
      lhs[i].push_back(p.second[i]);
    }
  }

#ifdef CVC4_ASSERTIONS
  for (const auto& row : lhs) { Assert(row.size() == nvars); }
  Assert(lhs.size() == rhs.size());
#endif

  if (lhs.size() > lhs[0].size())
  {
    return BVGaussElim::Result::INVALID;
  }

  Trace("bv-gauss-elim") << "Applying Gaussian Elimination..." << std::endl;
  Result ret = gaussElim(iprime, rhs, lhs);

  if (ret != BVGaussElim::Result::NONE && ret != BVGaussElim::Result::INVALID)
  {
    std::vector<Node> vvars;
    for (const auto& p : vars) { vvars.push_back(p.first); }
    Assert(nvars == vvars.size());
    Assert(nrows == lhs.size());
    Assert(nrows == rhs.size());
    NodeManager *nm = NodeManager::currentNM();
    if (ret == BVGaussElim::Result::UNIQUE)
    {
      for (size_t i = 0; i < nvars; ++i)
      {
        res[vvars[i]] = nm->mkConst<BitVector>(
            BitVector(utils::getSize(vvars[i]), rhs[i]));
      }
    }
    else
    {
      Assert(ret == BVGaussElim::Result::PARTIAL);

      for (size_t pcol = 0, prow = 0; pcol < nvars && prow < nrows;
           ++pcol, ++prow)
      {
        Assert(lhs[prow][pcol] == 0 || lhs[prow][pcol] == 1);
        while (pcol < nvars && lhs[prow][pcol] == 0) pcol += 1;
        if (pcol >= nvars)
        {
          Assert(rhs[prow] == 0);
          break;
        }
        if (lhs[prow][pcol] == 0)
        {
          Assert(rhs[prow] == 0);
          continue;
        }
        Assert(lhs[prow][pcol] == 1);
        std::vector<Node> stack;
        for (size_t i = pcol + 1; i < nvars; ++i)
        {
          if (lhs[prow][i] == 0) continue;
          /* Normalize (no negative numbers, hence no subtraction)
           * e.g., x = 4 - 2y  --> x = 4 + 9y (modulo 11) */
          Integer m = iprime - lhs[prow][i];
          Node bv = utils::mkConst(utils::getSize(vvars[i]), m);
          Node mult = nm->mkNode(kind::BITVECTOR_MULT, vvars[i], bv);
          stack.push_back(mult);
        }

        if (stack.empty())
        {
          res[vvars[pcol]] = nm->mkConst<BitVector>(
              BitVector(utils::getSize(vvars[pcol]), rhs[prow]));
        }
        else
        {
          Node tmp = stack.size() == 1
                         ? stack[0]
                         : nm->mkNode(kind::BITVECTOR_PLUS, stack);

          if (rhs[prow] != 0)
          {
            tmp = nm->mkNode(kind::BITVECTOR_PLUS,
                             utils::mkConst(
                                 utils::getSize(vvars[pcol]), rhs[prow]),
                             tmp);
          }
          Assert(!is_bv_const(tmp));
          res[vvars[pcol]] = nm->mkNode(kind::BITVECTOR_UREM, tmp, prime);
        }
      }
    }
  }
  return ret;
}

void BVGaussElim::gaussElimRewrite(std::vector<Node> &assertionsToPreprocess)
{
  std::vector<Node> assertions(assertionsToPreprocess);
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> equations;

  while (!assertions.empty())
  {
    Node a = assertions.back();
    assertions.pop_back();
    CVC4::Kind k = a.getKind();

    if (k == kind::AND)
    {
      for (const Node& aa : a)
      {
        assertions.push_back(aa);
      }
    }
    else if (k == kind::EQUAL)
    {
      Node urem;

      if (is_bv_const(a[1]) && a[0].getKind() == kind::BITVECTOR_UREM)
      {
        urem = a[0];
      }
      else if (is_bv_const(a[0]) && a[1].getKind() == kind::BITVECTOR_UREM)
      {
        urem = a[1];
      }
      else
      {
        continue;
      }

      if (urem[0].getKind() == kind::BITVECTOR_PLUS && is_bv_const(urem[1]))
      {
        equations[urem[1]].push_back(a);
      }
    }
  }

  std::unordered_map<Node, Node, NodeHashFunction> subst;

  for (const auto& eq : equations)
  {
    if (eq.second.size() <= 1) { continue; }

    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGaussElim::Result ret = gaussElimRewriteForUrem(eq.second, res);
    Trace("bv-gauss-elim") << "result: "
                           << (ret == BVGaussElim::Result::INVALID
                                   ? "INVALID"
                                   : (ret == BVGaussElim::Result::UNIQUE
                                          ? "UNIQUE"
                                          : (ret == BVGaussElim::Result::PARTIAL
                                                 ? "PARTIAL"
                                                 : "NONE")))
                           << std::endl;
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
        for (const Node& e : eq.second)
        {
          subst[e] = nm->mkConst<bool>(true);
        }
        /* add resulting constraints */
        for (const auto& p : res)
        {
          Node a = nm->mkNode(kind::EQUAL, p.first, p.second);
          Trace("bv-gauss-elim") << "added assertion: " << a << std::endl;
          assertionsToPreprocess.push_back(a);
        }
      }
    }
  }

  if (!subst.empty())
  {
    /* delete (= substitute with true) obsolete assertions */
    for (auto& a : assertionsToPreprocess)
    {
      a = a.substitute(subst.begin(), subst.end());
    }
  }
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
