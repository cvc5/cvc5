#include "util/bitvector.h"
#include "theory/bv/bvgauss.h"
#include "theory/bv/theory_bv_utils.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include <cxxtest/TestSuite.h>
#include <vector>

#include <iostream>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;
using namespace CVC4::smt;

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
    /* map result value to column index
     * e.g.:
     * 1 0 0 2  -> res = { 2, 0, 3}
     * 0 0 1 3 */
    std::vector< Integer > res = std::vector< Integer > (ncols, Integer(0));
    for (size_t i = 0; i < nrows; ++i)
      for (size_t j = 0; j < ncols; ++j)
      {
        if (reslhs[i][j] == 1) res[j] = resrhs[i];
        else TS_ASSERT (reslhs[i][j] == 0);
      }

    for (size_t i = 0; i < nrows; ++i)
    {
      Integer tmp = Integer(0);
      for (size_t j = 0; j < ncols; ++j)
        tmp = tmp.modAdd (lhs[i][j].modMultiply (res[j], prime), prime);
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
  ExprManager *d_em;
  NodeManager *d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;
  Node d_p;
  Node d_x;
  Node d_y;
  Node d_z;
  Node d_zero;
  Node d_one;
  Node d_two;
  Node d_three;
  Node d_four;
  Node d_five;
  Node d_six;
  Node d_seven;
  Node d_eight;
  Node d_nine;
  Node d_ten;
  Node d_twelve;
  Node d_eighteen;
  Node d_twentyfour;
  Node d_thirty;
  Node d_x_mul_one;
  Node d_x_mul_two;
  Node d_x_mul_four;
  Node d_y_mul_one;
  Node d_y_mul_three;
  Node d_y_mul_four;
  Node d_y_mul_five;
  Node d_y_mul_seven;
  Node d_z_mul_one;
  Node d_z_mul_three;
  Node d_z_mul_five;
  Node d_z_mul_twelve;
  Node d_z_mul_six;
  Node d_z_mul_nine;


public:

  TheoryBVGaussWhite () {}

  void setUp()
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);

    d_p = d_nm->mkConst<BitVector> (BitVector(16, 11u));
    d_x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    d_y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    d_z = d_nm->mkVar("z", d_nm->mkBitVectorType(16));

    d_zero = d_nm->mkConst<BitVector> (BitVector(16, 0u));
    d_one = d_nm->mkConst<BitVector> (BitVector(16, 1u));
    d_two = d_nm->mkConst<BitVector> (BitVector(16, 2u));
    d_three = d_nm->mkConst<BitVector> (BitVector(16, 3u));
    d_four = d_nm->mkConst<BitVector> (BitVector(16, 4u));
    d_five = d_nm->mkConst<BitVector> (BitVector(16, 5u));
    d_six = d_nm->mkConst<BitVector> (BitVector(16, 6u));
    d_seven = d_nm->mkConst<BitVector> (BitVector(16, 7u));
    d_eight = d_nm->mkConst<BitVector> (BitVector(16, 8u));
    d_nine = d_nm->mkConst<BitVector> (BitVector(16, 9u));
    d_ten = d_nm->mkConst<BitVector> (BitVector(16, 10u));
    d_twelve = d_nm->mkConst<BitVector> (BitVector(16, 12u));
    d_eighteen = d_nm->mkConst<BitVector> (BitVector(16, 18u));
    d_twentyfour = d_nm->mkConst<BitVector> (BitVector(16, 24u));
    d_thirty = d_nm->mkConst<BitVector> (BitVector(16, 30u));

    d_x_mul_one = d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_one);
    d_x_mul_two = d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_two);
    d_x_mul_four = d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four);
    d_y_mul_three = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three);
    d_y_mul_one = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_one);
    d_y_mul_four = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_four);
    d_y_mul_five = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_five);
    d_y_mul_seven = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven);
    d_z_mul_one = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_one);
    d_z_mul_three = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_three);
    d_z_mul_five = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_five);
    d_z_mul_six = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_six);
    d_z_mul_twelve = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_twelve);
    d_z_mul_nine = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_nine);


  }

  void tearDown()
  {
    (void) d_scope;
    d_p = Node::null();
    d_x = Node::null();
    d_y = Node::null();
    d_z = Node::null();
    d_zero = Node::null();
    d_one = Node::null();
    d_two = Node::null();
    d_three = Node::null();
    d_four = Node::null();
    d_five = Node::null();
    d_six = Node::null();
    d_seven = Node::null();
    d_eight = Node::null();
    d_nine = Node::null();
    d_ten = Node::null();
    d_twelve = Node::null();
    d_eighteen = Node::null();
    d_twentyfour = Node::null();
    d_thirty = Node::null();
    d_x_mul_one = Node::null();
    d_x_mul_two = Node::null();
    d_x_mul_four = Node::null();
    d_y_mul_one = Node::null();
    d_y_mul_four = Node::null();
    d_y_mul_seven = Node::null();
    d_y_mul_five = Node::null();
    d_y_mul_three = Node::null();
    d_z_mul_one = Node::null();
    d_z_mul_three = Node::null();
    d_z_mul_five = Node::null();
    d_z_mul_six = Node::null();
    d_z_mul_twelve = Node::null();
    d_z_mul_nine = Node::null();
    delete d_scope;
    delete d_smt;
    delete d_em;
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

  void testGaussElimUniqueZero3 ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 0 6   4        1 0 0   3
     *  0 0 0   0   -->  0 0 0   0
     *  4 0 6   3        0 0 1   2
     */
    rhs = { Integer(4), Integer(0), Integer(3) };
    lhs =
        {
          { Integer(2), Integer(0), Integer(6) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(0), Integer(6) }
        };
    std::cout << "matrix 10, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  0 0 0   0   -->  0 0 0   0
     *  4 6 0   3        0 0 1   2
     */
    rhs = { Integer(4), Integer(0), Integer(3) };
    lhs =
        {
          { Integer(2), Integer(6), Integer(0) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(6), Integer(0) }
        };
    std::cout << "matrix 11, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);
  }

  void testGaussElimUniqueZero4 ()
  {
    std::vector< Integer > rhs, resrhs;
    std::vector< std::vector< Integer >> lhs, reslhs;

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 0 0   0
     *  0 0 5   2
     */
    rhs = { Integer(5), Integer(0), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 12, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 3 5   8
     *  0 0 0   0
     */
    rhs = { Integer(5), Integer(8), Integer(0) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(3), Integer(5) },
          { Integer(0), Integer(0), Integer(0) }
        };
    std::cout << "matrix 13, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  0 3 5   8
     *  0 0 5   2
     */
    rhs = { Integer(0), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(3), Integer(5) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 14, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  0 0 0   0
     *  4 0 5   2
     */
    rhs = { Integer(5), Integer(0), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 15, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  2 0 5   8
     *  0 0 0   0
     */
    rhs = { Integer(5), Integer(8), Integer(0) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(0), Integer(0), Integer(0) }
        };
    std::cout << "matrix 16, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  2 0 5   8
     *  4 0 5   2
     */
    rhs = { Integer(0), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(0) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 17, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  0 0 0   0
     *  4 0 0   2
     */
    rhs = { Integer(5), Integer(0), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(0) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(0), Integer(0) }
        };
    std::cout << "matrix 18, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  2 3 0   8
     *  0 0 0   0
     */
    rhs = { Integer(5), Integer(8), Integer(0) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(0) },
          { Integer(2), Integer(3), Integer(0) },
          { Integer(0), Integer(0), Integer(0) }
        };
    std::cout << "matrix 18, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  2 3 0   8
     *  4 0 0   2
     */
    rhs = { Integer(0), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(0) },
          { Integer(2), Integer(3), Integer(0) },
          { Integer(4), Integer(0), Integer(0) }
        };
    std::cout << "matrix 19, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *     lhs    rhs  modulo 2
     *  ----^---   ^
     *  2  4   6   18     0 0 0   0
     *  4  5   6   24  =  0 1 0   0
     *  2  7  12   30     0 1 0   0
     */
    rhs = { Integer(18), Integer(24), Integer(30) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(2), Integer(7), Integer(12) }
        };
    std::cout << "matrix 20, modulo 2" << std::endl;
    resrhs = { Integer(0), Integer(0), Integer(0) };
    reslhs =
        {
          { Integer(0), Integer(1), Integer(0) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(2), rhs, lhs, BVGaussElim::Result::UNIQUE, &resrhs, &reslhs);
  }

  void testGaussElimUniquePartial ()
  {
    std::vector< Integer > rhs;
    std::vector< std::vector< Integer >> lhs;

    /*
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 0 6   4        1 0 0   3
     *  4 0 6   3        0 0 1   2
     */
    rhs = { Integer(4), Integer(3) };
    lhs =
        {
          { Integer(2), Integer(0), Integer(6) },
          { Integer(4), Integer(0), Integer(6) }
        };
    std::cout << "matrix 21, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /*
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  4 6 0   3        0 0 1   2
     */
    rhs = { Integer(4), Integer(3) };
    lhs =
        {
          { Integer(2), Integer(6), Integer(0) },
          { Integer(4), Integer(6), Integer(0) }
        };
    std::cout << "matrix 22, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);
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
    std::cout << "matrix 23, modulo 9" << std::endl;
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
    std::cout << "matrix 24, modulo 59" << std::endl;
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
    std::cout << "matrix 25, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, BVGaussElim::Result::NONE);
  }

  void testGaussElimNoneZero ()
  {
    std::vector< Integer > rhs, resrhs;
    std::vector< std::vector< Integer >> lhs, reslhs;

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 3 5   8
     *  0 0 5   2
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(3), Integer(5) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 26, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::NONE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  2 0 5   8
     *  4 0 5   2
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 27, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::NONE);

    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  2 3 0   8
     *  4 0 0   2
     */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(0) },
          { Integer(2), Integer(3), Integer(0) },
          { Integer(4), Integer(0), Integer(0) }
        };
    std::cout << "matrix 28, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::NONE);

  }

  void testGaussElimPartial ()
  {
    std::vector< Integer > rhs, resrhs;
    std::vector< std::vector< Integer >> lhs, reslhs;

    /*
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     */
    rhs = { Integer(7), Integer(9) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(9) },
          { Integer(0), Integer(1), Integer(3) }
        };
    std::cout << "matrix 29, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);

    /*
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 3 0   7   -->  1 3 0   7
     *  0 0 1   9        0 0 1   9
     */
    rhs = { Integer(7), Integer(9) };
    lhs =
        {
          { Integer(1), Integer(3), Integer(0) },
          { Integer(0), Integer(0), Integer(1) }
        };
    std::cout << "matrix 30, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);

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
    std::cout << "matrix 31, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);

    /*
     *     lhs    rhs  modulo { 3, 5, 7, 11, 17, 31, 59 }
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
    std::cout << "matrix 32, modulo 3" << std::endl;
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
    std::cout << "matrix 32, modulo 5" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(4) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(5), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 7" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(6) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(7), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 11" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(10) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 17" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(16) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(17), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 59" << std::endl;
    reslhs =
        {
          { Integer(1), Integer(0), Integer(58) },
          { Integer(0), Integer(1), Integer(2) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(59), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);

    /*
     *     lhs    rhs        lhs   rhs   modulo 3
     *  ----^---   ^        --^--   ^
     *   4  6 2   18   -->  1 0 2   0
     *   5  6 4   24        0 0 0   0
     *   7 12 2   30        0 0 0   0
     */
    rhs = { Integer(18), Integer(24), Integer(30) };
    lhs =
        {
          { Integer(4), Integer(6) , Integer(2)},
          { Integer(5), Integer(6) , Integer(4)},
          { Integer(7), Integer(12), Integer(2) }
        };
    std::cout << "matrix 33, modulo 3" << std::endl;
    resrhs = { Integer(0), Integer(0), Integer(0) };
    reslhs =
        {
          { Integer(1), Integer(0), Integer(2) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(0), Integer(0) }
        };
    testGaussElimX (
        Integer(3), rhs, lhs, BVGaussElim::Result::PARTIAL, &resrhs, &reslhs);
  }


  void testGaussElimRewriteForUremUnique ()
  {
    /*
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
              d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y_mul_one),
              d_z_mul_one),
          d_p),
        d_five);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
              d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_three),
              d_z_mul_five),
          d_p),
        d_eight);

    Node eq3 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_z_mul_five),
          d_p),
        d_two);

    std::vector< TNode > eqs = { eq1, eq2, eq3 };
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::UNIQUE);
    TS_ASSERT (res.size() == 3);
    TS_ASSERT (res[d_x] == d_nm->mkConst< BitVector > (BitVector (16, 3u)));
    TS_ASSERT (res[d_y] == d_nm->mkConst< BitVector > (BitVector (16, 4u)));
    TS_ASSERT (res[d_z] == d_nm->mkConst< BitVector > (BitVector (16, 9u)));
  }

  void testGaussElimRewriteForUremPartial1 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_z_mul_nine),
          d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_y_mul_one, d_z_mul_three),
          d_p),
        d_nine);

    std::vector< TNode > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_seven, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_nine));
    Node y1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_nine, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_three));

    Node x2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_eight));
    Node z2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_four));

    Node y3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_seven));
    Node z3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_five));

    /* result depends on order of variables in matrix */
    if (res.find (d_x) == res.end())
    {
      /*
       *  y z x           y z x
       *  0 9 1  7   -->  1 0 7  3
       *  1 3 0  9        0 1 5  2
       *
       *  z y x           z y x
       *  9 0 1  7   -->  1 0 5  2
       *  3 1 0  9        0 1 7  3
       */
      TS_ASSERT (res[d_y] == y3);
      TS_ASSERT (res[d_z] == z3);
    }
    else if (res.find (d_y) == res.end())
    {
      /*
       *  x z y           x z y
       *  1 9 0  7   -->  1 0 8  2
       *  0 3 1  9        0 1 4  3
       *
       *  z x y           z x y
       *  9 1 0  7   -->  1 0 4  3
       *  3 0 1  9        0 1 8  2
       */
      TS_ASSERT (res[d_x] == x2);
      TS_ASSERT (res[d_z] == z2);
    }
    else
    {
      TS_ASSERT (res.find (d_z) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT (res[d_x] == x1);
      TS_ASSERT (res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial1a ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_x, d_z_mul_nine),
          d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_y, d_z_mul_three),
          d_p),
        d_nine);

    std::vector< TNode > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_seven, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_nine));
    Node y1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_nine, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_three));

    Node x2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_eight));
    Node z2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_four));

    Node y3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_seven));
    Node z3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_five));


    /* result depends on order of variables in matrix */
    if (res.find (d_x) == res.end())
    {
      /*
       *  y z x           y z x
       *  0 9 1  7   -->  1 0 7  3
       *  1 3 0  9        0 1 5  2
       *
       *  z y x           z y x
       *  9 0 1  7   -->  1 0 5  2
       *  3 1 0  9        0 1 7  3
       */
      TS_ASSERT (res[d_y] == y3);
      TS_ASSERT (res[d_z] == z3);
    }
    else if (res.find (d_y) == res.end())
    {
      /*
       *  x z y           x z y
       *  1 9 0  7   -->  1 0 8  2
       *  0 3 1  9        0 1 4  3
       *
       *  z x y           z x y
       *  9 1 0  7   -->  1 0 4  3
       *  3 0 1  9        0 1 8  2
       */
      TS_ASSERT (res[d_x] == x2);
      TS_ASSERT (res[d_z] == z2);
    }
    else
    {
      TS_ASSERT (res.find (d_z) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT (res[d_x] == x1);
      TS_ASSERT (res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial2 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 3 0   7   -->  1 3 0   7
     *  0 0 1   9        0 0 1   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y_mul_three),
          d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_z_mul_one,
          d_p),
        d_nine);

    std::vector< TNode > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_seven, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three));
    Node y2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_six, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four));

    /* result depends on order of variables in matrix */
    if (res.find (d_x) == res.end())
    {
      /*
       *  x y z           x y z
       *  1 3 0  7   -->  1 3 0  7
       *  0 0 1  9        0 0 1  9
       *
       *  x z y           x z y
       *  1 0 3  7   -->  1 0 3  7
       *  0 1 0  9        0 1 0  9
       *
       *  z x y           z x y
       *  0 1 3  7   -->  1 0 0  9
       *  1 0 0  9        0 1 3  7
       */
      TS_ASSERT (res[d_y] == y2);
      TS_ASSERT (res[d_z] == d_nine);
    }
    else if (res.find (d_y) == res.end())
    {
      /*
       *  z y x           z y x
       *  0 3 1  7   -->  1 0 0  9
       *  1 0 0  9        0 1 4  6
       *
       *  y x z           y x z
       *  3 1 0  7   -->  1 4 0  6
       *  0 0 1  9        0 0 1  9
       *
       *  y z x           y z x
       *  3 0 1  7   -->  1 0 4  6
       *  0 1 0  9        0 1 0  9
       */
      TS_ASSERT (res[d_x] == x1);
      TS_ASSERT (res[d_z] == d_nine);
    }
    else
    {
      TS_ASSERT (false);
    }
  }

  void testGaussElimRewriteForUremPartial3 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 9   7
     *  2 3 5   8        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y),
            d_z_mul_one),
          d_p),
        d_five);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_three),
            d_z_mul_five),
          d_p),
        d_eight);

    std::vector< TNode > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_seven, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_nine));
    Node y1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_nine, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_three));
    Node x2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_eight));
    Node z2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_four));
    Node y3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_seven));
    Node z3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_five));

    /* result depends on order of variables in matrix */
    if (res.find (d_x) == res.end())
    {
      /*
       *  y z x           y z x
       *  1 1 1  5   -->  1 0 7  3
       *  3 5 2  8        0 1 5  2
       *
       *  z y x           z y x
       *  1 1 1  5   -->  1 0 5  2
       *  5 3 2  8        0 1 7  3
       */
      TS_ASSERT (res[d_y] == y3);
      TS_ASSERT (res[d_z] == z3);
    }
    else if (res.find (d_y) == res.end())
    {
      /*
       *  x z y           x z y
       *  1 1 1  5   -->  1 0 8  2
       *  2 5 3  8        0 1 4  3
       *
       *  z x y           z x y
       *  1 1 1  5   -->  1 0 4  3
       *  5 2 3  9        0 1 8  2
       */
      TS_ASSERT (res[d_x] == x2);
      TS_ASSERT (res[d_z] == z2);
    }
    else
    {
      TS_ASSERT (res.find (d_z) == res.end());
      /*
       *  x y z           x y z
       *  1 1 1  5   -->  1 0 9  7
       *  2 3 5  8        0 1 3  9
       *
       *  y x z           y x z
       *  1 1 1  5   -->  1 0 3  9
       *  3 2 5  8        0 1 9  7
       */
      TS_ASSERT (res[d_x] == x1);
      TS_ASSERT (res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial4 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *     lhs    rhs          lhs    rhs  modulo 11
     *  ----^---   ^         ---^---   ^
     *  2  4   6   18   -->  1 0 10    1
     *  4  5   6   24        0 1  2    4
     *  2  7  12   30        0 0  0    0
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_four),
            d_z_mul_six),
          d_p),
        d_eighteen);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_y_mul_five),
            d_z_mul_six),
          d_p),
        d_twentyfour);

    Node eq3 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_seven),
            d_z_mul_twelve),
          d_p),
        d_thirty);

    std::vector< TNode > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_one, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_ten));
    Node y1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_four, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two));
    Node x2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_six));
    Node z2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_six));
    Node y3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_six, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_two));
    Node z3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_ten, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_ten));

    /* result depends on order of variables in matrix */
    if (res.find (d_x) == res.end())
    {
      /*
       *  y  z x           y z  x
       *  4  6 2  18  -->  1 0  2   6
       *  5  6 4  24       0 1 10  10
       *  7 12 2  30       0 0  0   0
       *
       *  z  y x           z y  x
       *  6  4 2  18  -->  1 0 10  10
       *  6  5 4  24       0 1  2   6
       * 12 12 2  30       0 0  0   0
       *
       */
      TS_ASSERT (res[d_y] == y3);
      TS_ASSERT (res[d_z] == z3);
    }
    else if (res.find (d_y) == res.end())
    {
      /*
       *  x  z y           x z y
       *  2  6 4  18  -->  1 0 6  3
       *  4  6 5  24       0 1 6  2
       *  2 12 7  30       0 0 0  0
       *
       *  z x  y           z  x y
       *  6 2  4  18  -->  1  0 6  2
       *  6 4  5  24       0  1 6  3
       * 12 2 12  30       0  0 0  0
       *
       */
      TS_ASSERT (res[d_x] == x2);
      TS_ASSERT (res[d_z] == z2);
    }
    else
    {
      TS_ASSERT (res.find (d_z) == res.end());
      /*
       *  x y  z           x y  z
       *  2 4  6  18  -->  1 0 10  1
       *  4 5  6  24       0 1  2  4
       *  2 7 12  30       0 0  0  0
       *
       *  y x  z            y x  z
       *  4 2  6  18   -->  1 0  2 49
       *  5 4  6  24        0 1 10  1
       *  7 2 12  30        0 0  0  0
       */
      TS_ASSERT (res[d_x] == x1);
      TS_ASSERT (res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial5 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *     lhs    rhs         lhs   rhs  modulo 3
     *  ----^---   ^         --^--   ^
     *  2  4   6   18   -->  1 2 0   0
     *  4  5   6   24        0 0 0   0
     *  2  7  12   30        0 0 0   0
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_four),
            d_z_mul_six),
          d_three),
        d_eighteen);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_y_mul_five),
            d_z_mul_six),
          d_three),
        d_twentyfour);

    Node eq3 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_seven),
            d_z_mul_twelve),
          d_three),
        d_thirty);

    std::vector< TNode > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 1);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_NEG,
        d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_two));
    Node y2 = d_nm->mkNode(kind::BITVECTOR_NEG,
        d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_two));

    /* result depends on order of variables in matrix */
    if (res.find (d_x) == res.end())
    {
      /*
       *  y x  z           y x z
       *  4 2  6  18  -->  1 2 0 0
       *  5 4  6  24       0 0 0 0
       *  7 2 12  30       0 0 0 0
       *
         y  z x            y z x
       *  4  6 2  18  -->  1 0 2  0
       *  5  6 4  24       0 0 0  0
       *  7 12 2  30       0 0 0  0
       *
       *  z  y x           z y x
       *  6  4 2  18  -->  0 1 2  0
       *  6  5 4  24       0 0 0  0
       * 12 12 2  30       0 0 0  0
       *
       */
      TS_ASSERT (res[d_y] == y2);
    }
    else if (res.find (d_y) == res.end())
    {
      /*
       *  x y  z           x y z
       *  2 4  6  18  -->  1 2 0  0
       *  4 5  6  24       0 0 0  0
       *  2 7 12  30       0 0 0  0
       *
       *  x  z y           x z y
       *  2  6 4  18  -->  1 0 2  0
       *  4  6 5  24       0 0 0  0
       *  2 12 7  30       0 0 0  0
       *
       *  z x  y           z  x y
       *  6 2  4  18  -->  0  1 2  0
       *  6 4  5  24       0  0 0  0
       * 12 2 12  30       0  0 0  0
       *
       */
      TS_ASSERT (res[d_x] == x1);
    }
    else
    {
      TS_ASSERT (false);
    }
  }

  void testGaussElimRewriteForUremWithExprPartial ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node zero = mkZero (8);
    Node xx = d_nm->mkVar("xx", d_nm->mkBitVectorType(8));
    Node yy = d_nm->mkVar("yy", d_nm->mkBitVectorType(8));
    Node zz = d_nm->mkVar("zz", d_nm->mkBitVectorType(8));

    Node x = d_nm->mkNode(kind::BITVECTOR_CONCAT,
        zero, mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, xx), 7, 0));
    Node y = d_nm->mkNode(kind::BITVECTOR_CONCAT,
        zero, mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, yy), 7, 0));
    Node z = d_nm->mkNode(kind::BITVECTOR_CONCAT,
        zero, mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, zz), 7, 0));
    Node x_mul_one = d_nm->mkNode(kind::BITVECTOR_MULT, x, d_one);
    Node nine_mul_z = d_nm->mkNode(kind::BITVECTOR_MULT, d_nine, z);
    Node one_mul_y = d_nm->mkNode(kind::BITVECTOR_MULT, d_one, y);
    Node z_mul_three = d_nm->mkNode(kind::BITVECTOR_MULT, z, d_three);

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, x_mul_one, nine_mul_z),
          d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, one_mul_y, z_mul_three),
          d_p),
        d_nine);

    std::vector< TNode > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_seven, d_nm->mkNode(kind::BITVECTOR_MULT, z, d_nine));
    Node y1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_nine, d_nm->mkNode(kind::BITVECTOR_MULT, z, d_three));

    Node x2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, y, d_eight));
    Node z2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, y, d_four));

    Node y3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, x, d_seven));
    Node z3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, x, d_five));

    /* result depends on order of variables in matrix */
    if (res.find (x) == res.end())
    {
      /*
       *  y z x           y z x
       *  0 9 1  7   -->  1 0 7  3
       *  1 3 0  9        0 1 5  2
       *
       *  z y x           z y x
       *  9 0 1  7   -->  1 0 5  2
       *  3 1 0  9        0 1 7  3
       */
      TS_ASSERT (res[y] == y3);
      TS_ASSERT (res[z] == z3);
    }
    else if (res.find (y) == res.end())
    {
      /*
       *  x z y           x z y
       *  1 9 0  7   -->  1 0 8  2
       *  0 3 1  9        0 1 4  3
       *
       *  z x y           z x y
       *  9 1 0  7   -->  1 0 4  3
       *  3 0 1  9        0 1 8  2
       */
      TS_ASSERT (res[x] == x2);
      TS_ASSERT (res[z] == z2);
    }
    else
    {
      TS_ASSERT (res.find (z) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT (res[x] == x1);
      TS_ASSERT (res[y] == y1);
    }
  }

  void testGaussElimRewriteForUremNAryPartial ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node zero = mkZero (8);
    Node xx = d_nm->mkVar("xx", d_nm->mkBitVectorType(8));
    Node yy = d_nm->mkVar("yy", d_nm->mkBitVectorType(8));
    Node zz = d_nm->mkVar("zz", d_nm->mkBitVectorType(8));

    Node x = d_nm->mkNode(kind::BITVECTOR_CONCAT,
        zero, mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, xx), 7, 0));
    Node y = d_nm->mkNode(kind::BITVECTOR_CONCAT,
        zero, mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, yy), 7, 0));
    Node z = d_nm->mkNode(kind::BITVECTOR_CONCAT,
        zero, mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, zz), 7, 0));

    NodeBuilder<> nbx (d_nm, kind::BITVECTOR_MULT);
    nbx << d_x << d_one << x;
    Node x_mul_one_mul_xx = nbx.constructNode();
    NodeBuilder<> nby (d_nm, kind::BITVECTOR_MULT);
    nby << d_y << y << d_one;
    Node y_mul_yy_mul_one = nby.constructNode();
    NodeBuilder<> nbz (d_nm, kind::BITVECTOR_MULT);
    nbz << d_three << d_z << z;
    Node three_mul_z_mul_zz = nbz.constructNode();
    NodeBuilder<> nbz2 (d_nm, kind::BITVECTOR_MULT);
    nbz2 << d_z << d_nine << z;
    Node z_mul_nine_mul_zz = nbz2.constructNode();

    Node x_mul_xx = d_nm->mkNode(kind::BITVECTOR_MULT, d_x, x);
    Node y_mul_yy = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, y);
    Node z_mul_zz = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, z);

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            x_mul_one_mul_xx,
            z_mul_nine_mul_zz),
          d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            y_mul_yy_mul_one,
            three_mul_z_mul_zz),
          d_p),
        d_nine);

    std::vector< TNode > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_seven, d_nm->mkNode(kind::BITVECTOR_MULT, z_mul_zz, d_nine));
    Node y1 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_nine, d_nm->mkNode(kind::BITVECTOR_MULT, z_mul_zz, d_three));

    Node x2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, y_mul_yy, d_eight));
    Node z2 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, y_mul_yy, d_four));

    Node y3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_three, d_nm->mkNode(kind::BITVECTOR_MULT, x_mul_xx, d_seven));
    Node z3 = d_nm->mkNode(kind::BITVECTOR_SUB,
      d_two, d_nm->mkNode(kind::BITVECTOR_MULT, x_mul_xx, d_five));

    /* result depends on order of variables in matrix */
    if (res.find (x_mul_xx) == res.end())
    {
      /*
       *  y z x           y z x
       *  0 9 1  7   -->  1 0 7  3
       *  1 3 0  9        0 1 5  2
       *
       *  z y x           z y x
       *  9 0 1  7   -->  1 0 5  2
       *  3 1 0  9        0 1 7  3
       */
      TS_ASSERT (res[y_mul_yy] == y3);
      TS_ASSERT (res[z_mul_zz] == z3);
    }
    else if (res.find (y_mul_yy) == res.end())
    {
      /*
       *  x z y           x z y
       *  1 9 0  7   -->  1 0 8  2
       *  0 3 1  9        0 1 4  3
       *
       *  z x y           z x y
       *  9 1 0  7   -->  1 0 4  3
       *  3 0 1  9        0 1 8  2
       */
      TS_ASSERT (res[x_mul_xx] == x2);
      TS_ASSERT (res[z_mul_zz] == z2);
    }
    else
    {
      TS_ASSERT (res.find (z_mul_zz) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT (res[x_mul_xx] == x1);
      TS_ASSERT (res[y_mul_yy] == y1);
    }
  }


  // TODO test cases for invalid input
};
