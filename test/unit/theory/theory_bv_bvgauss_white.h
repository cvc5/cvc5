#include "util/bitvector.h"
#include "theory/bv/bvgauss.h"
#include <cxxtest/TestSuite.h>
#include <vector>

#include <iostream>

using namespace CVC4;
using namespace theory;
using namespace bv;

static void
print_matrix_dbg (std::vector< Integer > & rhs,
                  std::vector< std::vector< Integer >> & lhs)
{
  for (size_t m = 0, nrows = lhs.size(), ncols = lhs[0].size(); m < nrows; ++m)
  {
    for (size_t n = 0; n < ncols; ++n)
    {
      std::cout << " " << lhs[m][n];
    }
    std::cout << " " << rhs[m];
    std::cout << std::endl;
  }
}

static void 
testGaussElimX (Integer prime,
                std::vector< Integer > rhs,
                std::vector< std::vector< Integer >> lhs,
                BVGaussElim::Result expected,
                std::vector< Integer > * rrhs = nullptr,
                std::vector< std::vector< Integer >> * rlhs = nullptr)
{
  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();
  BVGaussElim::Result ret;
  std::vector< Integer > resrhs;
  std::vector< std::vector< Integer >> reslhs;


  std::cout << "Input: " << std::endl;
  print_matrix_dbg (rhs, lhs);

  ret = BVGaussElim::gaussElim (prime, rhs, lhs, resrhs, reslhs);

  std::cout << "Result: " << std::endl;
  print_matrix_dbg (resrhs, reslhs);

  TS_ASSERT_EQUALS (expected, ret);

  if (expected == BVGaussElim::Result::UNIQUE)
  {
    for (size_t i = 0; i < nrows; ++i)
    {
      Integer tmp = Integer(0);
      for (size_t j = 0; j < ncols; ++j)
      {
        tmp = tmp.modAdd (lhs[i][j].modMultiply (resrhs[j], prime), prime);
        if (prime != 1 && i == j)
        {
          TS_ASSERT (reslhs[i][j] == 1);
        }
        else
        {
          TS_ASSERT (reslhs[i][j] == 0);
        }
      }
      TS_ASSERT (tmp == rhs[i].euclidianDivideRemainder (prime));
    }
  }
  if (rrhs != nullptr && rlhs != nullptr)
  {
    for (size_t i = 0; i < nrows; ++i)
    {
      for (size_t j = 0; j < ncols; ++j)
      {
        TS_ASSERT (reslhs[i][j] == (*rlhs)[i][j]);
      }
      TS_ASSERT (resrhs[i] == (*rrhs)[i]);
    }
  }
}

template <class T>
static void 
testGaussElimT (Integer prime,
                std::vector< Integer > rhs,
                std::vector< std::vector< Integer >> lhs)
{
  std::vector< Integer > resrhs;
  std::vector< std::vector< Integer >> reslhs;
  TS_ASSERT_THROWS (
      BVGaussElim::gaussElim (prime, rhs, lhs, resrhs, reslhs), T);
}

class TheoryBVGaussWhite : public CxxTest::TestSuite
{
public:
  
  TheoryBVGaussWhite () {}

  void setUp ()
  {
  }

  void tearDown ()
  {
  }

  void testGaussElimMod ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs   rhs  modulo { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(2), Integer(3), Integer(5) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 0, modulo 0" << std::endl;  // throws
    testGaussElimT<AssertionException> (Integer(0), rhs, lhs);
    std::cout << "matrix 0, modulo 1" << std::endl;
    testGaussElimX (Integer(1), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 0, modulo 2" << std::endl;
    testGaussElimX (Integer(2), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 0, modulo 3" << std::endl;
    testGaussElimX (Integer(3), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 0, modulo 4" << std::endl; // no inverse
    testGaussElimX (Integer(4), rhs, lhs, BVGaussElim::Result::NONE);
    std::cout << "matrix 0, modulo 5" << std::endl;
    testGaussElimX (Integer(5), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 0, modulo 6" << std::endl; // no inverse
    testGaussElimX (Integer(6), rhs, lhs, BVGaussElim::Result::NONE);
    std::cout << "matrix 0, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 0, modulo 8" << std::endl; // no inverse
    testGaussElimX (Integer(8), rhs, lhs, BVGaussElim::Result::NONE);
    std::cout << "matrix 0, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 0, modulo 10" << std::endl; // no inverse
    testGaussElimX (Integer(10), rhs, lhs, BVGaussElim::Result::NONE);
    std::cout << "matrix 0, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);
  }

  void testGaussElimUniqueDone ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;
    /*
     *   lhs     rhs        lhs    rhs  modulo 17
     *  --^---    ^        --^--    ^
     *  1 0 0    4   -->   1 0 0    4
     *  0 1 0   15         0 1 0   15
     *  0 0 1    3         0 0 1    3
     */
    rhs = { Integer(4), Integer(15), Integer(3) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(0) },
          { Integer(0), Integer(1), Integer(0) },
          { Integer(0), Integer(0), Integer(1) }
        };
    std::cout << "matrix 1, modulo 17" << std::endl;
    testGaussElimX (Integer(17), rhs, lhs, BVGaussElim::Result::UNIQUE);
  }
    
  void testGaussElimUnique ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs     rhs  modulo { 11,17,59 }
     *  --^---    ^
     *  2 4  6   18
     *  4 5  6   24
     *  3 1 -2    4
     */
    rhs = { Integer(18), Integer(24), Integer(4) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(3), Integer(1), Integer(-2) }
        };
    std::cout << "matrix 2, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 2, modulo 17" << std::endl;
    testGaussElimX (Integer(17), rhs, lhs, BVGaussElim::Result::UNIQUE);
    std::cout << "matrix 2, modulo 59" << std::endl;
    testGaussElimX (Integer(59), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *      lhs       rhs         lhs     rhs   modulo 11
     *  -----^-----    ^        ---^---    ^
     *  1  1  2   0    1   -->  1 0 0 0    1
     *  2 -1  0   1   -2        0 1 0 0    2
     *  1 -1 -1  -2    4        0 0 1 0   -1
     *  2 -1  2  -1    0        0 0 0 1   -2
     */
    rhs = { Integer(1), Integer(-2), Integer(4), Integer(0) };
    lhs =
        {
          { Integer(1), Integer(1),  Integer(2),  Integer(0) },
          { Integer(2), Integer(-1), Integer(0),  Integer(1) },
          { Integer(1), Integer(-1), Integer(-1), Integer(-2) },
          { Integer(2), Integer(-1), Integer(2),  Integer(-1) }
        };
    std::cout << "matrix 3, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

  }

  void testGaussElimUniqueZero1 ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  0 4 5   2   -->  1 0 0   4
     *  1 1 1   5        0 1 0   3
     *  3 2 5   8        0 0 1   9
     */
    rhs = { Integer(2), Integer(5), Integer(8) };
    lhs =
        {
          { Integer(0), Integer(4), Integer(5) },
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 4, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   4
     *  0 4 5   2        0 1 0   3
     *  3 2 5   8        0 0 1   9
     */
    rhs = { Integer(5), Integer(2), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(0), Integer(4), Integer(5) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 5, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   4
     *  3 2 5   8        0 1 0   9
     *  0 4 5   2        0 0 1   3
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) },
          { Integer(0), Integer(4), Integer(5) }
        };
    std::cout << "matrix 6, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

  }

  void testGaussElimUniqueZero2 ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  0 0 5   2        1 0 0   10
     *  1 1 1   5   -->  0 1 0   10
     *  3 2 5   8        0 0 1   7
     */
    rhs = { Integer(2), Integer(5), Integer(8) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(5) },
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 7, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   10
     *  0 0 5   2        0 1 0   10
     *  3 2 5   8        0 0 1   7
     */
    rhs = { Integer(5), Integer(2), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(0), Integer(0), Integer(5) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 8, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   10
     *  3 2 5   8        0 1 0   10
     *  0 0 5   2        0 0 1    7
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 9, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);
  }

  void testGaussElimNone ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs     rhs       modulo 9
     *  --^---    ^
     *  2 4  6   18   -->  not coprime (no inverse)
     *  4 5  6   24
     *  3 1 -2    4
     */
    rhs = { Integer(18), Integer(24), Integer(4) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(3), Integer(1), Integer(-2) }
        };
    std::cout << "matrix 2, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, BVGaussElim::Result::NONE);

    /*
     *     lhs    rhs       modulo 59
     *  ----^---   ^
     *  1 -2  -6   12   --> no solution
     *  2  4  12  -17
     *  1 -4 -12   22
     */
    rhs = { Integer(12), Integer(-17), Integer(22) };
    lhs =
        {
          { Integer(1), Integer(-2), Integer(-6) },
          { Integer(2), Integer(4), Integer(12) },
          { Integer(1), Integer(-4), Integer(-12) }
        };
    std::cout << "matrix 10, modulo 59" << std::endl;
    testGaussElimX (Integer(59), rhs, lhs, BVGaussElim::Result::NONE);

    /*
     *     lhs    rhs       modulo 9
     *  ----^---   ^
     *  2  4   6   18   --> not coprime (no inverse)
     *  4  5   6   24
     *  2  7  12   30
     */
    rhs = { Integer(18), Integer(24), Integer(30) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(2), Integer(7), Integer(12) }
        };
    std::cout << "matrix 11, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, BVGaussElim::Result::NONE);
  }

  void testGaussElimPartial ()
  {
    std::vector< Integer > rhs, resrhs;
    std::vector< std::vector< Integer >> lhs, reslhs;

    /*
     *     lhs    rhs  modulo { 2, 3, 5, 7, 11, 17, 31, 59 }
     *  ----^---   ^
     *  2  4   6   18
     *  4  5   6   24
     *  2  7  12   30
     */
    rhs = { Integer(18), Integer(24), Integer(30) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(2), Integer(7), Integer(12) }
        };
    //std::cout << "matrix 11, modulo 2" << std::endl;
    //resrhs = { Integer(0), Integer(0), Integer(0) };
    //reslhs =
    //    {
    //      { Integer(1), Integer(2), Integer(0) },
    //      { Integer(0), Integer(0), Integer(0) },
    //      { Integer(0), Integer(0), Integer(0) }
    //    };
    //testGaussElimX (
    //    Integer(2), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 11, modulo 3" << std::endl;
    resrhs = { Integer(0), Integer(0), Integer(0) };
    reslhs =
        {
          { Integer(1), Integer(2), Integer(0) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(3), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    resrhs = { Integer(1), Integer(4), Integer(0) };
    std::cout << "matrix 11, modulo 5" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(4) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(5), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 11, modulo 7" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(6) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(7), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 11, modulo 11" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(10) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 11, modulo 17" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(16) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(17), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 11, modulo 59" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(58) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(59), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);

    /*
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 9   7
     *  2 3 5   8        0 1 3   9
     */
    rhs = { Integer(5), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(2), Integer(3), Integer(5) }
        };
    std::cout << "matrix 12, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);
  }
};
