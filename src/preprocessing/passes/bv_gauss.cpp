/*********************                                                        */
/*! \file bv_gauss.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Gaussian Elimination preprocessing pass.
 **
 ** Simplify a given equation system modulo a (prime) number via Gaussian
 ** Elimination if possible.
 **/

#include "preprocessing/passes/bv_gauss.h"

#include "expr/node.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

#include <unordered_map>
#include <vector>


using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

namespace CVC4 {
namespace preprocessing {
namespace passes {

namespace {

bool is_bv_const(Node n)
{
  if (n.isConst()) { return true; }
  return Rewriter::rewrite(n).getKind() == kind::CONST_BITVECTOR;
}

Node get_bv_const(Node n)
{
  Assert(is_bv_const(n));
  return Rewriter::rewrite(n);
}

Integer get_bv_const_value(Node n)
{
  Assert(is_bv_const(n));
  return get_bv_const(n).getConst<BitVector>().getValue();
}

}  // namespace

/**
 * Determines if an overflow may occur in given 'expr'.
 *
 * Returns 0 if an overflow may occur, and the minimum required
 * bit-width such that no overflow occurs, otherwise.
 *
 * Note that it would suffice for this function to be Boolean.
 * However, it is handy to determine the minimum required bit-width for
 * debugging purposes.
 *
 * Note: getMinBwExpr assumes that 'expr' is rewritten.
 *
 * If not, all operators that are removed via rewriting (e.g., ror, rol, ...)
 * will be handled via the default case, which is not incorrect but also not
 * necessarily the minimum.
 */
unsigned BVGauss::getMinBwExpr(Node expr)
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
          const unsigned size = bv::utils::getSize(n);
          const unsigned low = bv::utils::getExtractLow(n);
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
          if (w > bv::utils::getSize(n)) { return 0; } /* overflow */
          visited[n] = w;
          break;
        }

        case kind::BITVECTOR_CONCAT:
        {
          unsigned i, wnz, nc;
          for (i = 0, wnz = 0, nc = n.getNumChildren() - 1; i < nc; ++i)
          {
            unsigned wni = bv::utils::getSize(n[i]);
            if (n[i] != bv::utils::mkZero(wni)) { break; }
            /* sum of all bit-widths of leading zero concats */
            wnz += wni;
          }
          /* Do not consider leading zero concats, i.e.,
           * min bw of current concat is determined as
           *   min bw of first non-zero term
           *   plus actual bw of all subsequent terms */
          visited[n] = bv::utils::getSize(n) + visited[n[i]]
                       - bv::utils::getSize(n[i]) - wnz;
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
          if (w > bv::utils::getSize(n)) { return 0; } /* overflow */
          visited[n] = w;
          break;
        }

        default:
        {
          /* BITVECTOR_UDIV_TOTAL (since x / 0 = -1)
           * BITVECTOR_NOT
           * BITVECTOR_NEG
           * BITVECTOR_SHL */
          visited[n] = bv::utils::getSize(n);
        }
      }
    }
  }
  Assert(visited.find(expr) != visited.end());
  return visited[expr];
}

/**
 * Apply Gaussian Elimination modulo a (prime) number.
 * The given equation system is represented as a matrix of Integers.
 *
 * Note that given 'prime' does not have to be prime but can be any
 * arbitrary number. However, if 'prime' is indeed prime, GE is guaranteed
 * to succeed, which is not the case, otherwise.
 *
 * Returns INVALID if GE can not be applied, UNIQUE and PARTIAL if GE was
 * successful, and NONE, otherwise.
 *
 * Vectors 'rhs' and 'lhs' represent the right hand side and left hand side
 * of the given matrix, respectively. The resulting matrix (in row echelon
 * form) is stored in 'rhs' and 'lhs', i.e., the given matrix is overwritten
 * with the resulting matrix.
 */
BVGauss::Result BVGauss::gaussElim(Integer prime,
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
    return BVGauss::Result::UNIQUE;
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
      for (size_t k = 0; k < pcol; ++k)
      {
        Assert(lhs[j][k] == 0);
      }
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
            return BVGauss::Result::INVALID; /* not coprime */
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
        return BVGauss::Result::NONE;
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

  if (ispart)
  {
    return BVGauss::Result::PARTIAL;
  }

  return BVGauss::Result::UNIQUE;
}

/**
 * Apply Gaussian Elimination on a set of equations modulo some (prime)
 * number given as bit-vector equations.
 *
 * IMPORTANT: Applying GE modulo some number (rather than modulo 2^bw)
 * on a set of bit-vector equations is only sound if this set of equations
 * has a solution that does not produce overflows. Consequently, we only
 * apply GE if the given bit-width guarantees that no overflows can occur
 * in the given set of equations.
 *
 * Note that the given set of equations does not have to be modulo a prime
 * but can be modulo any arbitrary number. However, if it is indeed modulo
 * prime, GE is guaranteed to succeed, which is not the case, otherwise.
 *
 * Returns INVALID if GE can not be applied, UNIQUE and PARTIAL if GE was
 * successful, and NONE, otherwise.
 *
 * The resulting constraints are stored in 'res' as a mapping of unknown
 * to result (modulo prime). These mapped results are added as constraints
 * of the form 'unknown = mapped result' in applyInternal.
 */
BVGauss::Result BVGauss::gaussElimRewriteForUrem(
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
      return BVGauss::Result::INVALID;
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
          n0 = bv::utils::mkOne(bv::utils::getSize(n));
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
  if (nvars == 0)
  {
    return BVGauss::Result::INVALID;
  }
  size_t nrows = vars.begin()->second.size();
#ifdef CVC4_ASSERTIONS
  for (const auto& p : vars)
  {
    Assert(p.second.size() == nrows);
  }
#endif

  if (nrows < 1)
  {
    return BVGauss::Result::INVALID;
  }

  for (size_t i = 0; i < nrows; ++i)
  {
    for (const auto& p : vars)
    {
      lhs[i].push_back(p.second[i]);
    }
  }

#ifdef CVC4_ASSERTIONS
  for (const auto& row : lhs)
  {
    Assert(row.size() == nvars);
  }
  Assert(lhs.size() == rhs.size());
#endif

  if (lhs.size() > lhs[0].size())
  {
    return BVGauss::Result::INVALID;
  }

  Trace("bv-gauss-elim") << "Applying Gaussian Elimination..." << std::endl;
  BVGauss::Result ret = gaussElim(iprime, rhs, lhs);

  if (ret != BVGauss::Result::NONE && ret != BVGauss::Result::INVALID)
  {
    std::vector<Node> vvars;
    for (const auto& p : vars) { vvars.push_back(p.first); }
    Assert(nvars == vvars.size());
    Assert(nrows == lhs.size());
    Assert(nrows == rhs.size());
    NodeManager *nm = NodeManager::currentNM();
    if (ret == BVGauss::Result::UNIQUE)
    {
      for (size_t i = 0; i < nvars; ++i)
      {
        res[vvars[i]] = nm->mkConst<BitVector>(
            BitVector(bv::utils::getSize(vvars[i]), rhs[i]));
      }
    }
    else
    {
      Assert(ret == BVGauss::Result::PARTIAL);

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
          Node bv = bv::utils::mkConst(bv::utils::getSize(vvars[i]), m);
          Node mult = nm->mkNode(kind::BITVECTOR_MULT, vvars[i], bv);
          stack.push_back(mult);
        }

        if (stack.empty())
        {
          res[vvars[pcol]] = nm->mkConst<BitVector>(
              BitVector(bv::utils::getSize(vvars[pcol]), rhs[prow]));
        }
        else
        {
          Node tmp = stack.size() == 1
                         ? stack[0]
                         : nm->mkNode(kind::BITVECTOR_PLUS, stack);

          if (rhs[prow] != 0)
          {
            tmp = nm->mkNode(kind::BITVECTOR_PLUS,
                             bv::utils::mkConst(
                                 bv::utils::getSize(vvars[pcol]), rhs[prow]),
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

BVGauss::BVGauss(PreprocessingPassContext* preprocContext,
                 const std::string& name)
    : PreprocessingPass(preprocContext, name)
{
}

PreprocessingPassResult BVGauss::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> assertions(assertionsToPreprocess->ref());
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
  std::vector<Node>& atpp = assertionsToPreprocess->ref();

  for (const auto& eq : equations)
  {
    if (eq.second.size() <= 1) { continue; }

    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret = gaussElimRewriteForUrem(eq.second, res);
    Trace("bv-gauss-elim") << "result: "
                           << (ret == BVGauss::Result::INVALID
                                   ? "INVALID"
                                   : (ret == BVGauss::Result::UNIQUE
                                          ? "UNIQUE"
                                          : (ret == BVGauss::Result::PARTIAL
                                                 ? "PARTIAL"
                                                 : "NONE")))
                           << std::endl;
    if (ret != BVGauss::Result::INVALID)
    {
      NodeManager *nm = NodeManager::currentNM();
      if (ret == BVGauss::Result::NONE)
      {
        atpp.clear();
        atpp.push_back(nm->mkConst<bool>(false));
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
          atpp.push_back(a);
        }
      }
    }
  }

  if (!subst.empty())
  {
    /* delete (= substitute with true) obsolete assertions */
    for (auto& a : atpp)
    {
      a = a.substitute(subst.begin(), subst.end());
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
