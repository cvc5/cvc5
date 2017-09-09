#include "theory/bv/bvgauss.h"
#include <iostream>

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
      if (j > pcol && reslhs[i][j] != 0) ispart = true;
  }
  if (ispart) return BVGaussElim::Result::PARTIAL;

  return BVGaussElim::Result::UNIQUE;
}


//void
//BVGaussElim::gaussElimRewrite (std::vector<Node> & assertionsToPreprocess)
//{
//}

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

