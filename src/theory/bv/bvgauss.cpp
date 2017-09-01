#include "theory/bv/bvgauss.h"
#include <iostream>

using namespace CVC4;
using namespace std;

static void
print_matrix_dbg (vector< Integer > & rhs, vector< vector< Integer >> & lhs)
{
  cout << endl;
  for (size_t m = 0, nrows = lhs.size(), ncols = lhs[0].size(); m < nrows; ++m)
  {
    cout <<"##";
    for (size_t n = 0; n < ncols; ++n)
    {
        cout << " " << lhs[m][n];
    }
    cout << " " << rhs[m];
    cout << endl;
  }
}

// FIXME: make this a static helper function?
bool
gaussElim (Integer prime,
           vector< Integer > & rhs,
           vector< vector< Integer >> & lhs,
           vector< Integer > & res)

{
  Assert (prime > 0);
  Assert (lhs.size());
  Assert (lhs.size() == rhs.size());
  Assert (lhs.size() <= lhs[0].size());


  /* special case: zero ring */
  if (prime == 1)
  {
    res = vector< Integer > (rhs.size(), Integer(0));
    return true;
  }

  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();
  vector< vector< Integer >> tmplhs = vector< vector< Integer>> (lhs);

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

  res = vector< Integer > (rhs);

  /* pivot = tmplhs[i][i] */
  for (size_t i = 0; i < nrows; ++i)
  {
    print_matrix_dbg (res, tmplhs);

    /* tmplhs[j][i]: element in pivot column */
    for (size_t j = i; j < nrows; ++j)
    {
#ifdef CVC4_ASSERTIONS
      for (size_t k = 0; k < i; ++k)
        Assert (tmplhs[j][k] == 0);
#endif
      /* normalize element in pivot column to modulo prime */
      tmplhs[j][i] = tmplhs[j][i].euclidianDivideRemainder (prime);
      /* exchange rows if first elem of first row is 0 */
      if (j == 0 && tmplhs[j][i] == 0)
      {
        for (size_t k = i+1; k < nrows; ++k)
          if (tmplhs[k][i] != 0)
          {
            Integer itmp = res[j];
            res[j] = res[k];
            res[k] = itmp;
            vector< Integer > tmp = tmplhs[j];
            tmplhs[j] = tmplhs[k];
            tmplhs[k] = tmp;
            break;
          }
      }
      /* (1) */
      if (tmplhs[j][i] != 0)
      {
       if (tmplhs[j][i] != 1)
        {
          Integer inv = tmplhs[j][i].modInverse (prime);
          if (inv == -1) return false;  /* not coprime */
          for (size_t k = i; k < ncols; ++k)
          {
            tmplhs[j][k] = tmplhs[j][k].modMultiply (inv, prime);
            if (j <= i) continue;  /** pivot */
            tmplhs[j][k] = tmplhs[j][k].modAdd (-tmplhs[i][k], prime);
          }
          res[j] = res[j].modMultiply (inv, prime);
          if (j > i) res[j] = res[j].modAdd (-res[i], prime);
        }
        /* (2) */
        else if (j != i)
        {
          for (size_t k = i; k < ncols; ++k)
            tmplhs[j][k] = tmplhs[j][k].modAdd (-tmplhs[i][k], prime);
          res[j] = res[j].modAdd (-res[i], prime);
        }
      }
    }

  print_matrix_dbg (res, tmplhs);
    /* (3) */
    for (size_t j = 0; j < i; ++j)
    {
      Integer mul = tmplhs[j][i];
      if (mul != 0)
      {
        for (size_t k = i; k < ncols; ++k)
          tmplhs[j][k] = tmplhs[j][k].modAdd (-tmplhs[i][k] * mul, prime);
        res[j] = res[j].modAdd (-res[i] * mul, prime);
      }
    }
  }
  print_matrix_dbg (res, tmplhs);
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

