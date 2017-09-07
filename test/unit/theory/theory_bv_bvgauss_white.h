#include "util/bitvector.h"
#include "theory/bv/bvgauss.h"
#include <cxxtest/TestSuite.h>
#include <vector>

#include <iostream>

using namespace CVC4;

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
                bool expected)
{
  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();
  bool ret;
  std::vector< Integer > resrhs;
  std::vector< std::vector< Integer >> reslhs;


  std::cout << "Input: " << std::endl;
  print_matrix_dbg (rhs, lhs);

  ret = theory::bv::BVGaussElim::gaussElim (prime, rhs, lhs, resrhs, reslhs);

  std::cout << "Result: " << std::endl;
  print_matrix_dbg (resrhs, reslhs);

  TS_ASSERT_EQUALS (expected, ret);

  if (expected)
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
      theory::bv::BVGaussElim::gaussElim (prime, rhs, lhs, resrhs, reslhs), T);
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

  void testGaussElim ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    //   lhs     rhs        lhs    rhs  modulo { 9,17,59 }
    //  --^---    ^        --^--    ^
    //  2 4  6   18   -->  1 0 0    4
    //  4 5  6   24        0 1 0   15
    //  3 1 -2    4        0 0 1    3
    rhs = { Integer(18), Integer(24), Integer(4) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(3), Integer(1), Integer(-2) }
        };
    std::cout << "matrix 0, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, false);
    std::cout << "matrix 0, modulo 17" << std::endl;
    testGaussElimX (Integer(17), rhs, lhs, true);
    std::cout << "matrix 0, modulo 59" << std::endl;
    testGaussElimX (Integer(59), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs  modulo { 1,2,3,4,5,6,7,8,9,10,11 }
    //  --^--   ^        --^--   ^
    //  1 1 1   5   -->  1 0 0   3
    //  2 3 5   8        0 1 0   4
    //  4 0 5   2        0 0 1   9
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(2), Integer(3), Integer(5) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 1, modulo 1" << std::endl;
    testGaussElimX (Integer(1), rhs, lhs, true);
    std::cout << "matrix 1, modulo 2" << std::endl;
    testGaussElimX (Integer(2), rhs, lhs, true);
    std::cout << "matrix 1, modulo 3" << std::endl;
    testGaussElimX (Integer(3), rhs, lhs, true);
    std::cout << "matrix 1, modulo 4" << std::endl;
    testGaussElimX (Integer(4), rhs, lhs, false);
    std::cout << "matrix 1, modulo 5" << std::endl;
    testGaussElimX (Integer(5), rhs, lhs, true);
    std::cout << "matrix 1, modulo 6" << std::endl;
    testGaussElimX (Integer(6), rhs, lhs, false);
    std::cout << "matrix 1, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, true);
    std::cout << "matrix 1, modulo 8" << std::endl;
    testGaussElimX (Integer(8), rhs, lhs, false);
    std::cout << "matrix 1, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, true);
    std::cout << "matrix 1, modulo 10" << std::endl;
    testGaussElimX (Integer(10), rhs, lhs, false);
    std::cout << "matrix 1, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs   modulo 11
    //  --^--   ^        --^--   ^
    //  0 4 5   2   -->  1 0 0   4
    //  1 1 1   5        0 1 0   3
    //  3 2 5   8        0 0 1   9
    rhs = { Integer(2), Integer(5), Integer(8) };
    lhs =
        {
          { Integer(0), Integer(4), Integer(5) },
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 2, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs   modulo 11
    //  --^--   ^        --^--   ^
    //  1 1 1   5   -->  1 0 0   4
    //  0 4 5   2        0 1 0   3
    //  3 2 5   8        0 0 1   9
    rhs = { Integer(5), Integer(2), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(0), Integer(4), Integer(5) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 3, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs   modulo 11
    //  --^--   ^        --^--   ^
    //  1 1 1   5   -->  1 0 0   4
    //  3 2 5   8        0 1 0   9
    //  0 4 5   2        0 0 1   3
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) },
          { Integer(0), Integer(4), Integer(5) }
        };
    std::cout << "matrix 4, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs   modulo 11
    //  --^--   ^        --^--   ^
    //  0 0 5   2        1 0 0   10
    //  1 1 1   5   -->  0 1 0   10
    //  3 2 5   8        0 0 1   7
    rhs = { Integer(2), Integer(5), Integer(8) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(5) },
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 5, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs   modulo 11
    //  --^--   ^        --^--   ^
    //  1 1 1   5   -->  1 0 0   10
    //  0 0 5   2        0 1 0   10
    //  3 2 5   8        0 0 1   7
    rhs = { Integer(5), Integer(2), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(0), Integer(0), Integer(5) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 6, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //   lhs   rhs        lhs   rhs   modulo 11
    //  --^--   ^        --^--   ^
    //  1 1 1   5   -->  1 0 0   10
    //  3 2 5   8        0 1 0   10
    //  0 0 5   2        0 0 1    7
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 7, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);

    //      lhs       rhs        lhs     rhs   modulo 11
    //  -----^-----    ^        ---^---   ^
    //  1  1  2   0    1   -->  1 0 0 0   1
    //  2 -1  0   1   -2        0 1 0 0   2
    //  1 -1 -1  -2    4        0 0 1 0  -1
    //  2 -1  2  -1    0        0 0 0 1  -2
    rhs = { Integer(1), Integer(-2), Integer(4), Integer(0) };
    lhs =
        {
          { Integer(1), Integer(1),  Integer(2),  Integer(0) },
          { Integer(2), Integer(-1), Integer(0),  Integer(1) },
          { Integer(1), Integer(-1), Integer(-1), Integer(-2) },
          { Integer(2), Integer(-1), Integer(2),  Integer(-1) }
        };
    std::cout << "matrix 8, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);
  }

  void testGaussElimEx ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;
    /* 
     * Modulo value must be greater than 0 -> throwsAssertion Exception.
     *
     *    lhs  =  rhs  modulo 0
     *   --^--     ^
     *   1 1 1     5
     *   3 2 5     8
     *   0 4 5     2
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) },
          { Integer(0), Integer(4), Integer(5) }
        };
    std::cout << "matrix 4, modulo 0" << std::endl;
    testGaussElimT<AssertionException> (Integer(0), rhs, lhs);
  }
};

