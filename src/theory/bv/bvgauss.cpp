#include "theory/bv/bvgauss.h"

#include <iostream>
#include <stack>

#include "theory/bv/theory_bv_utils.h"

using namespace CVC4;
using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {

BVGaussElim::Result
BVGaussElim:: gaussElim (Integer prime,
                         vector< Integer > & rhs,
                         vector< vector< Integer >> & lhs,
                         vector< Integer > & resrhs,
                         vector< vector< Integer >> & reslhs)

{
  Assert (prime > 0);
  Assert (lhs.size());
  Assert (lhs.size() == rhs.size());
  Assert (lhs.size() <= lhs[0].size());

  /* special case: zero ring */
  if (prime == 1)
  {
    resrhs = vector< Integer > (rhs.size(), Integer(0));
    reslhs = vector< vector< Integer >> (
        lhs.size(), vector< Integer > (lhs[0].size(), Integer(0)));
    return BVGaussElim::Result::UNIQUE;
  }

  resrhs = vector< Integer > (rhs);
  reslhs = vector< vector< Integer>> (lhs);


  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();

#ifdef CVC4_ASSERTIONS
  for (size_t i = 1; i < nrows; ++i)
    Assert (lhs[i].size() == ncols);
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
      for (size_t k = 0; k < pcol; ++k)
        Assert (reslhs[j][k] == 0);
#endif
      /* normalize element in pivot column to modulo prime */
      reslhs[j][pcol] = reslhs[j][pcol].euclidianDivideRemainder (prime);
      /* exchange rows if pivot elem is 0 */
      if (j == prow)
      {
        while (reslhs[j][pcol] == 0)
        {
          for (size_t k = prow+1; k < nrows; ++k)
          {
            reslhs[k][pcol] = reslhs[k][pcol].euclidianDivideRemainder (prime);
            if (reslhs[k][pcol] != 0)
            {
              Integer itmp = resrhs[j];
              resrhs[j] = resrhs[k];
              resrhs[k] = itmp;
              vector< Integer > tmp = reslhs[j];
              reslhs[j] = reslhs[k];
              reslhs[k] = tmp;
              break;
            }
          }
          if (pcol >= ncols-1) break;
          if (reslhs[j][pcol] == 0)
          {
            pcol += 1;
            if (reslhs[j][pcol] != 0)
              reslhs[j][pcol] = reslhs[j][pcol].euclidianDivideRemainder (prime);
          }
        }
      }

      /* (1) */
      if (reslhs[j][pcol] != 0)
      {
       if (reslhs[j][pcol] != 1)
        {
          Integer inv = reslhs[j][pcol].modInverse (prime);
          if (inv == -1) return BVGaussElim::Result::NONE;  /* not coprime */
          for (size_t k = pcol; k < ncols; ++k)
          {
            reslhs[j][k] = reslhs[j][k].modMultiply (inv, prime);
            if (j <= prow) continue;  /** pivot */
            reslhs[j][k] = reslhs[j][k].modAdd (-reslhs[prow][k], prime);
          }
          resrhs[j] = resrhs[j].modMultiply (inv, prime);
          if (j > prow) resrhs[j] = resrhs[j].modAdd (-resrhs[prow], prime);
        }
        /* (2) */
        else if (j != prow)
        {
          for (size_t k = pcol; k < ncols; ++k)
            reslhs[j][k] = reslhs[j][k].modAdd (-reslhs[prow][k], prime);
          resrhs[j] = resrhs[j].modAdd (-resrhs[prow], prime);
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
          reslhs[j][k] = reslhs[j][k].modAdd (-reslhs[prow][k] * mul, prime);
        resrhs[j] = resrhs[j].modAdd (-resrhs[prow] * mul, prime);
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
      resrhs[i] = resrhs[i].euclidianDivideRemainder (prime);
      if (resrhs[i] != 0) return BVGaussElim::Result::NONE;
      continue;
    }
    for (size_t j = i; j < ncols; ++j)
    {
      if (reslhs[i][j] >= prime || reslhs[i][j] <= -prime)
        reslhs[i][j] = reslhs[i][j].euclidianDivideRemainder (prime);
      if (j > pcol && reslhs[i][j] != 0) ispart = true;
    }
  }
  if (ispart) return BVGaussElim::Result::PARTIAL;

  return BVGaussElim::Result::UNIQUE;
}

BVGaussElim::Result
BVGaussElim::gaussElimRewriteForUrem (
    vector< TNode > & equations,
    unordered_map< Node, Node, NodeHashFunction > & res)
{
  Integer prime;
  unordered_map< TNode, vector< Integer >, TNodeHashFunction > vars;
  size_t neqs = equations.size();
  vector< Integer > resrhs, rhs;
  vector< vector< Integer >> reslhs, lhs =
    vector< vector< Integer >> (neqs, vector< Integer >());

  res = unordered_map< Node, Node, NodeHashFunction >();

  for (size_t i = 0; i < neqs; ++i)
  {
    TNode eq = equations[i];
    Assert (eq.getKind() == kind::EQUAL);
    TNode urem;

    if (eq[0].getKind() == kind::BITVECTOR_UREM)
    {
      Assert (eq[1].getKind() == kind::CONST_BITVECTOR);
      urem = eq[0];
      rhs.push_back (eq[1].getConst< BitVector >().getValue());
    }
    else
    {
      Assert (eq[1].getKind() == kind::BITVECTOR_UREM);
      Assert (eq[0].getKind() == kind::CONST_BITVECTOR);
      urem = eq[1];
      rhs.push_back (eq[0].getConst< BitVector >().getValue());
    }

    Assert (urem[1].getKind() == kind::CONST_BITVECTOR);
    Assert (i == 0 || urem[1].getConst< BitVector >().getValue() == prime);
    if (i == 0) prime = urem[1].getConst< BitVector >().getValue();

    unordered_map< TNode, TNode, TNodeHashFunction > tmp;
    bool isvalid = true;
    stack< TNode > stack;
    stack.push (urem[0]);
    while (!stack.empty())
    {
      TNode n = stack.top();
      stack.pop();
      CVC4::Kind k = n.getKind();
      cout << "kind " << k << endl;
      if (k == kind::BITVECTOR_PLUS)
      {
        for (size_t j = 0, nchild = n.getNumChildren(); j < nchild; ++j)
          stack.push (n[j]);
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
          NodeBuilder<> nb (NodeManager::currentNM(), k);

          for (size_t j = 0; j < nchild; ++j)
          {
            if (n0 == Node::null()
                && n[j].getKind() == kind::CONST_BITVECTOR)
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
        CVC4::Kind kn0 = n0.getKind();
        CVC4::Kind kn1 = n1.getKind();
        if (kn0 == kind::CONST_BITVECTOR)
        {
          Assert (kn1 != kind::CONST_BITVECTOR);
          tmp[n1] = n0;
        }
        else if (kn1 == kind::CONST_BITVECTOR)
        {
          Assert (kn0 != kind::CONST_BITVECTOR);
          tmp[n0] = n1;
        }
        else
        {
          isvalid = false;
          break;
        }
      }
      else
      {
        cout << "asdf " << endl;
        tmp[n] = utils::mkOne(utils::getSize(n));
      }
    }

    if (!isvalid) continue;

    // Note: "var" is not necessarily a VARIABLE but can be an arbitrary expr

    for (auto p : tmp)
    {
      TNode var = p.first;
      TNode val = p.second;
      if (i > 0 && vars.find (var) == vars.end())
      {
        for (size_t j = 0; j < i; ++j) 
          vars[var].push_back (Integer(0));
      }
      vars[var].push_back (val.getConst< BitVector >().getValue());
    }

    for (auto p : vars)
    {
      if (tmp.find (p.first) == tmp.end())
        vars[p.first].push_back (Integer(0));
    }
  }

  size_t nvars = vars.size();
  size_t nrows = vars.begin()->second.size();
#ifdef CVC4_ASSERTIONS
  for (auto p : vars) Assert (p.second.size() == nrows);
#endif

  if (nrows < 1) return BVGaussElim::Result::NONE;

  for (size_t i = 0; i < nrows; ++i)
  {
    for (auto p : vars)
      lhs[i].push_back (p.second[i]);
  }

#ifdef CVC4_ASSERTIONS
  for (size_t i = 0; i < nrows; ++i)
    Assert (lhs[i].size() == nvars);
  Assert (lhs.size() == rhs.size());
#endif

  Result ret = gaussElim (prime, rhs, lhs, resrhs, reslhs);
  if (ret != BVGaussElim::Result::NONE)
  {
    vector< TNode > vvars;
    for (auto p : vars) vvars.push_back (p.first);
    Assert (nvars == vvars.size());
    Assert (lhs[0].size() == reslhs[0].size());
    Assert (nrows == lhs.size());
    Assert (lhs.size() == reslhs.size());
    Assert (nrows == rhs.size());
    Assert (rhs.size() == resrhs.size());
    NodeManager *nm = NodeManager::currentNM();
    if (ret == BVGaussElim::Result::UNIQUE)
    {
      for (size_t i = 0; i < nvars; ++i)
      {
        res[vvars[i]] = nm->mkConst< BitVector > (
            BitVector (utils::getSize (vvars[i]), resrhs[i]));
      }
    }
    else
    {
      Assert (ret == BVGaussElim::Result::PARTIAL);
      for (size_t pcol = 0, prow = 0;
           pcol < nvars && pcol < nrows;
           ++pcol, ++prow)
      {
        Assert (reslhs[prow][pcol] == 0 || reslhs[prow][pcol] == 1);
        while (pcol < nvars && reslhs[prow][pcol] == 0) pcol += 1;
        if (pcol >= nvars) { Assert (resrhs[prow] == 0); break; }
        if (reslhs[prow][pcol] == 0) { Assert (resrhs[prow] == 0); continue; }
        Assert (reslhs[prow][pcol] == 1);
        stack< Node > stack;
        while (reslhs[prow][pcol] == 0) pcol += 1;
        for (size_t i = pcol + 1; i < nvars; ++i)
        {
          if (reslhs[prow][i] == 0) continue;
          Node bv = nm->mkConst< BitVector > (
              BitVector (utils::getSize(vvars[i]), reslhs[prow][i]));
          Node mult = nm->mkNode (kind::BITVECTOR_MULT, vvars[i], bv);
          stack.push (mult);
        }
        if (stack.empty())
        {
          res[vvars[pcol]] = nm->mkConst< BitVector > (
              BitVector (utils::getSize(vvars[pcol]), resrhs[prow]));
        }
        else
        {
          Node tmp = stack.top();
          stack.pop();
          if (resrhs[prow] == 0)
            tmp = nm->mkNode (kind::BITVECTOR_NEG, tmp);
          else
            tmp = nm->mkNode (kind::BITVECTOR_SUB,
                nm->mkConst< BitVector >(
                  BitVector (utils::getSize(vvars[pcol]), resrhs[prow])),
                tmp);
          while (!stack.empty())
          {
            tmp = nm->mkNode (kind::BITVECTOR_SUB, tmp, stack.top());
            stack.pop();
          }
          res[vvars[pcol]] = tmp;
        }
      }
    }
  }
  return ret;
}

void
BVGaussElim::gaussElimRewrite (std::vector<Node> & assertionsToPreprocess)
{
  stack< TNode > assertions;
  unordered_map< BitVector, vector< TNode >, BitVectorHashFunction > equations;
  vector< Integer > resrhs;
  vector< vector< Integer >> reslhs;

  for (size_t i = 0, nass = assertionsToPreprocess.size(); i < nass; ++i)
    assertions.push (assertionsToPreprocess[i]);

  while (!assertions.empty())
  {
    TNode a = assertions.top();
    CVC4::Kind k = a.getKind();
    assertions.pop();

    if (k == kind::AND)
    {
      for (size_t i = 0, nchild = a.getNumChildren(); i < nchild; ++i)
        assertions.push (a[i]);
    }
    else if (k == kind::EQUAL)
    {
      CVC4::Kind k0 = a[0].getKind();
      CVC4::Kind k1 = a[1].getKind();
      TNode urem;

      if (k0 == kind::CONST_BITVECTOR && k1 == kind::BITVECTOR_UREM)
        urem = a[1];
      else if (k1 == kind::CONST_BITVECTOR && k0 == kind::BITVECTOR_UREM)
        urem = a[0];
      else
        continue;

      if (urem[0].getKind() == kind::BITVECTOR_PLUS
          && urem[1].getKind() == kind::CONST_BITVECTOR)
      {
        BitVector u = urem[1].getConst< BitVector >();
        if (equations.find(u) == equations.end())
          equations[u] = vector< TNode >();
        equations[u].push_back (a);
      }
    }
  }

  for (auto e : equations)
  {
    // TODO
  }
}

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

