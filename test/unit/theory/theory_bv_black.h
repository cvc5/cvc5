#include "util/bitvector.h"
#include "theory/bv/bvgauss.h"
#include <cxxtest/TestSuite.h>
#include <vector>

#include <iostream>

using namespace CVC4;

static void 
testGaussElimX (Integer prime,
                std::vector< Integer > rhs,
                std::vector< std::vector< Integer >> lhs,
                bool expected)
{
  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();
  std::vector< Integer > result;

  TS_ASSERT_EQUALS (expected, gaussElim (prime, rhs, lhs, result));

  if (expected)
  {
    for (size_t i = 0; i < nrows; ++i)
    {
      Integer tmp = Integer(0);
      for (size_t j = 0; j < ncols; ++j)
        tmp = tmp.modAdd (lhs[i][j].modMultiply (result[j], prime), prime);
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
  std::vector< Integer > result;
  TS_ASSERT_THROWS (
      gaussElim (prime, rhs, lhs, result), T);
}

class TheoryBVBlack : public CxxTest::TestSuite
{

public:
  
  TheoryBVBlack () {}

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
    //   lhs     rhs        lhs    rhs    modulo 17
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
    std::cout << "matrix 0, modulo 17" << std::endl;
    testGaussElimX (Integer(17), rhs, lhs, true);
    std::cout << "matrix 0, modulo 59" << std::endl;
    testGaussElimX (Integer(59), rhs, lhs, true);
    std::cout << "matrix 0, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, false);

    //   lhs   rhs        lhs   rhs   modulo 11
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
    std::cout << "matrix 1, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, true);
    std::cout << "matrix 1, modulo 10" << std::endl;
    testGaussElimX (Integer(10), rhs, lhs, false);
    std::cout << "matrix 1, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, true);
    std::cout << "matrix 1, modulo 8" << std::endl;
    testGaussElimX (Integer(8), rhs, lhs, false);
    std::cout << "matrix 1, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, true);
    std::cout << "matrix 1, modulo 6" << std::endl;
    testGaussElimX (Integer(6), rhs, lhs, false);
    std::cout << "matrix 1, modulo 5" << std::endl;
    testGaussElimX (Integer(5), rhs, lhs, true);
    std::cout << "matrix 1, modulo 4" << std::endl;
    testGaussElimX (Integer(4), rhs, lhs, false);
    std::cout << "matrix 1, modulo 3" << std::endl;
    testGaussElimX (Integer(3), rhs, lhs, true);
    std::cout << "matrix 1, modulo 2" << std::endl;
    testGaussElimX (Integer(2), rhs, lhs, true);
    std::cout << "matrix 1, modulo 1" << std::endl;
    testGaussElimX (Integer(1), rhs, lhs, true);

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

    //   lhs   rhs         modulo 0
    //  --^--   ^        
    //  1 1 1   5   -->   throws AssertionException
    //  3 2 5   8        
    //  0 4 5   2        
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) },
          { Integer(0), Integer(4), Integer(5) }
        };
    std::cout << "matrix 4, modulo 11" << std::endl;
    testGaussElimT<AssertionException> (Integer(0), rhs, lhs);

    //   lhs    rhs        modulo 11
    //  --^--    ^        
    //  0 1 1    5   -->  throws AssertionException
    //  0 2 5    8        
    //  0 4 10  16        
    rhs = { Integer(5), Integer(8), Integer(16) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(2), Integer(5) },
          { Integer(0), Integer(4), Integer(10) }
        };
    std::cout << "matrix 5, modulo 11" << std::endl;
    testGaussElimT<AssertionException> (Integer(11), rhs, lhs);

    //   lhs    rhs        modulo 11
    //  --^--    ^        
    //  1 0 1    5   -->  throws AssertionException
    //  2 0 5    8        
    //  4 0 10  16        
    rhs = { Integer(5), Integer(8), Integer(16) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(4), Integer(0), Integer(10) }
        };
    std::cout << "matrix 6, modulo 11" << std::endl;
    testGaussElimT<AssertionException> (Integer(11), rhs, lhs);

    //   lhs    rhs        modulo 11
    //  --^--    ^        
    //  1 1  0   5   -->  throws AssertionException
    //  2 5  0   8        
    //  4 10 0  16        
    rhs = { Integer(5), Integer(8), Integer(16) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(0)},
          { Integer(2), Integer(5), Integer(0)},
          { Integer(4), Integer(10), Integer(0)}
        };
    std::cout << "matrix 7, modulo 11" << std::endl;
    testGaussElimT<AssertionException> (Integer(11), rhs, lhs);
  }

};

