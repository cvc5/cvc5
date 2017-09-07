#include "theory/bv/bvgauss.h"
#include <iostream>

using namespace CVC4;
using namespace std;

// FIXME: make this a private member function
bool
gaussElim (Integer prime,
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
    return true;
  }

  resrhs = vector< Integer > (rhs);
  reslhs = vector< vector< Integer>> (lhs);


  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();

#ifdef CVC4_ASSERTIONS
  for (size_t i = 1; i < nrows; ++i)
    Assert (lhs[i].size() == ncols);
  for (size_t k = 0; k < ncols; ++k)
  {
    size_t cnt0 = 0;
    for (size_t i = 0; i < nrows; i++)
      if (lhs[i][k] == 0) cnt0 += 1;
    Assert (cnt0 < nrows);
  }
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

  /* pivot = reslhs[i][i] */
  for (size_t i = 0; i < ncols; ++i)
  {
    /* reslhs[j][i]: element in pivot column */
    for (size_t j = i; j < nrows; ++j)
    {
#ifdef CVC4_ASSERTIONS
      for (size_t k = 0; k < i; ++k)
        Assert (reslhs[j][k] == 0);
#endif
      /* normalize element in pivot column to modulo prime */
      reslhs[j][i] = reslhs[j][i].euclidianDivideRemainder (prime);
      /* exchange rows if pivot elem is 0 */
      if (j == i && reslhs[j][i] == 0)
      {
        for (size_t k = i+1; k < nrows; ++k)
          if (reslhs[k][i] != 0)
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

      /* (1) */
      if (reslhs[j][i] != 0)
      {
       if (reslhs[j][i] != 1)
        {
          Integer inv = reslhs[j][i].modInverse (prime);
          if (inv == -1) return false;  /* not coprime */
          for (size_t k = i; k < ncols; ++k)
          {
            reslhs[j][k] = reslhs[j][k].modMultiply (inv, prime);
            if (j <= i) continue;  /** pivot */
            reslhs[j][k] = reslhs[j][k].modAdd (-reslhs[i][k], prime);
          }
          resrhs[j] = resrhs[j].modMultiply (inv, prime);
          if (j > i) resrhs[j] = resrhs[j].modAdd (-resrhs[i], prime);
        }
        /* (2) */
        else if (j != i)
        {
          for (size_t k = i; k < ncols; ++k)
            reslhs[j][k] = reslhs[j][k].modAdd (-reslhs[i][k], prime);
          resrhs[j] = resrhs[j].modAdd (-resrhs[i], prime);
        }
      }
    }

    /* (3) */
    for (size_t j = 0; j < i; ++j)
    {
      Integer mul = reslhs[j][i];
      if (mul != 0)
      {
        for (size_t k = i; k < ncols; ++k)
          reslhs[j][k] = reslhs[j][k].modAdd (-reslhs[i][k] * mul, prime);
        resrhs[j] = resrhs[j].modAdd (-resrhs[i] * mul, prime);
      }
    }
  }
  return true;
}

namespace CVC4 {
namespace theory {
namespace bv {


//static void
//BVGaussElim::
//gaussElimRewrite (std::vector<Node> & assertionsToPreprocess)
//{
//}

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

