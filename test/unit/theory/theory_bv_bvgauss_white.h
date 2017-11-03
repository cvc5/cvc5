/*********************                                                        */
/*! \file theory_bv_bvgauss_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for Gaussian Elimination preprocessing pass.
 **
 ** Unit tests for Gaussian Elimination preprocessing pass.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/bvgauss.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <vector>


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
  Node d_one32;
  Node d_two32;
  Node d_three32;
  Node d_four32;
  Node d_five32;
  Node d_six32;
  Node d_seven32;
  Node d_eight32;
  Node d_nine32;
  Node d_ten32;
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

    d_zero = mkZero(16);

    d_p = mkConcat(d_zero, d_nm->mkConst<BitVector> (BitVector(16, 11u)));
    d_x = mkConcat(d_zero, d_nm->mkVar("x", d_nm->mkBitVectorType(16)));
    d_y = mkConcat(d_zero, d_nm->mkVar("y", d_nm->mkBitVectorType(16)));
    d_z = mkConcat(d_zero, d_nm->mkVar("z", d_nm->mkBitVectorType(16)));

    d_one = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 1u)));
    d_two = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 2u)));
    d_three = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 3u)));
    d_four = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 4u)));
    d_five = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 5u)));
    d_six = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 6u)));
    d_seven = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 7u)));
    d_eight = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 8u)));
    d_nine = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 9u)));
    d_ten = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 10u)));
    d_twelve = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 12u)));
    d_eighteen = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 18u)));
    d_twentyfour = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 24u)));
    d_thirty = mkConcat(d_zero,
        d_nm->mkConst<BitVector> (BitVector(16, 30u)));

    d_one32 = d_nm->mkConst<BitVector> (BitVector(32, 1u));
    d_two32 = d_nm->mkConst<BitVector> (BitVector(32, 2u));
    d_three32 = d_nm->mkConst<BitVector> (BitVector(32, 3u));
    d_four32 = d_nm->mkConst<BitVector> (BitVector(32, 4u));
    d_five32 = d_nm->mkConst<BitVector> (BitVector(32, 5u));
    d_six32 = d_nm->mkConst<BitVector> (BitVector(32, 6u));
    d_seven32 = d_nm->mkConst<BitVector> (BitVector(32, 7u));
    d_eight32 = d_nm->mkConst<BitVector> (BitVector(32, 8u));
    d_nine32 = d_nm->mkConst<BitVector> (BitVector(32, 9u));
    d_ten32 = d_nm->mkConst<BitVector> (BitVector(32, 10u));

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
    d_one32 = Node::null();
    d_two32 = Node::null();
    d_three32 = Node::null();
    d_four32 = Node::null();
    d_five32 = Node::null();
    d_six32 = Node::null();
    d_seven32 = Node::null();
    d_eight32 = Node::null();
    d_nine32 = Node::null();
    d_ten32 = Node::null();
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

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */
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
    
    /* -------------------------------------------------------------------
     *   lhs     rhs        lhs    rhs  modulo 17
     *  --^---    ^        --^--    ^
     *  1 0 0    4   -->   1 0 0    4
     *  0 1 0   15         0 1 0   15
     *  0 0 1    3         0 0 1    3
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs     rhs  modulo { 11,17,59 }
     *  --^---    ^
     *  2 4  6   18
     *  4 5  6   24
     *  3 1 -2    4
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *      lhs       rhs         lhs     rhs   modulo 11
     *  -----^-----    ^        ---^---    ^
     *  1  1  2   0    1   -->  1 0 0 0    1
     *  2 -1  0   1   -2        0 1 0 0    2
     *  1 -1 -1  -2    4        0 0 1 0   -1
     *  2 -1  2  -1    0        0 0 0 1   -2
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  0 4 5   2   -->  1 0 0   4
     *  1 1 1   5        0 1 0   3
     *  3 2 5   8        0 0 1   9
     * ------------------------------------------------------------------- */
    rhs = { Integer(2), Integer(5), Integer(8) };
    lhs =
        {
          { Integer(0), Integer(4), Integer(5) },
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 4, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   4
     *  0 4 5   2        0 1 0   3
     *  3 2 5   8        0 0 1   9
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(2), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(0), Integer(4), Integer(5) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 5, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   4
     *  3 2 5   8        0 1 0   9
     *  0 4 5   2        0 0 1   3
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  0 0 5   2        1 0 0   10
     *  1 1 1   5   -->  0 1 0   10
     *  3 2 5   8        0 0 1   7
     * ------------------------------------------------------------------- */
    rhs = { Integer(2), Integer(5), Integer(8) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(5) },
          { Integer(1), Integer(1), Integer(1) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 7, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   10
     *  0 0 5   2        0 1 0   10
     *  3 2 5   8        0 0 1   7
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(2), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(0), Integer(0), Integer(5) },
          { Integer(3), Integer(2), Integer(5) }
        };
    std::cout << "matrix 8, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   10
     *  3 2 5   8        0 1 0   10
     *  0 0 5   2        0 0 1    7
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 0 6   4        1 0 0   3
     *  0 0 0   0   -->  0 0 0   0
     *  4 0 6   3        0 0 1   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(4), Integer(0), Integer(3) };
    lhs =
        {
          { Integer(2), Integer(0), Integer(6) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(0), Integer(6) }
        };
    std::cout << "matrix 10, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  0 0 0   0   -->  0 0 0   0
     *  4 6 0   3        0 0 1   2
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 0 0   0
     *  0 0 5   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(0), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 12, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 3 5   8
     *  0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(8), Integer(0) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(3), Integer(5) },
          { Integer(0), Integer(0), Integer(0) }
        };
    std::cout << "matrix 13, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  0 3 5   8
     *  0 0 5   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(0), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(0) },
          { Integer(0), Integer(3), Integer(5) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 14, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  0 0 0   0
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(0), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 15, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  2 0 5   8
     *  0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(8), Integer(0) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(0), Integer(0), Integer(0) }
        };
    std::cout << "matrix 16, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  2 0 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(0), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(0) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 17, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  0 0 0   0
     *  4 0 0   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(0), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(0) },
          { Integer(0), Integer(0), Integer(0) },
          { Integer(4), Integer(0), Integer(0) }
        };
    std::cout << "matrix 18, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  2 3 0   8
     *  0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(8), Integer(0) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(0) },
          { Integer(2), Integer(3), Integer(0) },
          { Integer(0), Integer(0), Integer(0) }
        };
    std::cout << "matrix 18, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  2 3 0   8
     *  4 0 0   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(0), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(0), Integer(0) },
          { Integer(2), Integer(3), Integer(0) },
          { Integer(4), Integer(0), Integer(0) }
        };
    std::cout << "matrix 19, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *     lhs    rhs  modulo 2
     *  ----^---   ^
     *  2  4   6   18     0 0 0   0
     *  4  5   6   24  =  0 1 0   0
     *  2  7  12   30     0 1 0   0
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 0 6   4        1 0 0   3
     *  4 0 6   3        0 0 1   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(4), Integer(3) };
    lhs =
        {
          { Integer(2), Integer(0), Integer(6) },
          { Integer(4), Integer(0), Integer(6) }
        };
    std::cout << "matrix 21, modulo 7" << std::endl;
    testGaussElimX (Integer(7), rhs, lhs, BVGaussElim::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  4 6 0   3        0 1 0   2
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs     rhs       modulo 9
     *  --^---    ^
     *  2 4  6   18   -->  not coprime (no inverse)
     *  4 5  6   24
     *  3 1 -2    4
     * ------------------------------------------------------------------- */
    rhs = { Integer(18), Integer(24), Integer(4) };
    lhs =
        {
          { Integer(2), Integer(4), Integer(6) },
          { Integer(4), Integer(5), Integer(6) },
          { Integer(3), Integer(1), Integer(-2) }
        };
    std::cout << "matrix 23, modulo 9" << std::endl;
    testGaussElimX (Integer(9), rhs, lhs, BVGaussElim::Result::NONE);

    /* -------------------------------------------------------------------
     *     lhs    rhs       modulo 59
     *  ----^---   ^
     *  1 -2  -6   12   --> no solution
     *  2  4  12  -17
     *  1 -4 -12   22
     * ------------------------------------------------------------------- */
    rhs = { Integer(12), Integer(-17), Integer(22) };
    lhs =
        {
          { Integer(1), Integer(-2), Integer(-6) },
          { Integer(2), Integer(4), Integer(12) },
          { Integer(1), Integer(-4), Integer(-12) }
        };
    std::cout << "matrix 24, modulo 59" << std::endl;
    testGaussElimX (Integer(59), rhs, lhs, BVGaussElim::Result::NONE);

    /* -------------------------------------------------------------------
     *     lhs    rhs       modulo 9
     *  ----^---   ^
     *  2  4   6   18   --> not coprime (no inverse)
     *  4  5   6   24
     *  2  7  12   30
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 3 5   8
     *  0 0 5   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(0), Integer(1), Integer(1) },
          { Integer(0), Integer(3), Integer(5) },
          { Integer(0), Integer(0), Integer(5) }
        };
    std::cout << "matrix 26, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::NONE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  2 0 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(8), Integer(2) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(1) },
          { Integer(2), Integer(0), Integer(5) },
          { Integer(4), Integer(0), Integer(5) }
        };
    std::cout << "matrix 27, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::NONE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  2 3 0   8
     *  4 0 0   2
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */
    rhs = { Integer(7), Integer(9) };
    lhs =
        {
          { Integer(1), Integer(0), Integer(9) },
          { Integer(0), Integer(1), Integer(3) }
        };
    std::cout << "matrix 29, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 3 0   7   -->  1 3 0   7
     *  0 0 1   9        0 0 1   9
     * ------------------------------------------------------------------- */
    rhs = { Integer(7), Integer(9) };
    lhs =
        {
          { Integer(1), Integer(3), Integer(0) },
          { Integer(0), Integer(0), Integer(1) }
        };
    std::cout << "matrix 30, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 9   7
     *  2 3 5   8        0 1 3   9
     * ------------------------------------------------------------------- */
    rhs = { Integer(5), Integer(8) };
    lhs =
        {
          { Integer(1), Integer(1), Integer(1) },
          { Integer(2), Integer(3), Integer(5) }
        };
    std::cout << "matrix 31, modulo 11" << std::endl;
    testGaussElimX (Integer(11), rhs, lhs, BVGaussElim::Result::PARTIAL);

    /* -------------------------------------------------------------------
     *     lhs    rhs  modulo { 3, 5, 7, 11, 17, 31, 59 }
     *  ----^---   ^
     *  2  4   6   18
     *  4  5   6   24
     *  2  7  12   30
     * ------------------------------------------------------------------- */
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

    /* -------------------------------------------------------------------
     *     lhs    rhs        lhs   rhs   modulo 3
     *  ----^---   ^        --^--   ^
     *   4  6 2   18   -->  1 0 2   0
     *   5  6 4   24        0 0 0   0
     *   7 12 2   30        0 0 0   0
     * ------------------------------------------------------------------- */
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
    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */

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

    std::vector< Node > eqs = { eq1, eq2, eq3 };
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::UNIQUE);
    TS_ASSERT (res.size() == 3);
    TS_ASSERT (res[d_x] == d_three32);
    TS_ASSERT (res[d_y] == d_four32);
    TS_ASSERT (res[d_z] == d_nine32);
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

    std::vector< Node > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)), d_p);
    Node y1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_nine32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)), d_p);

    Node x2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)), d_p);
    Node z2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)), d_p);

    Node y3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)), d_p);
    Node z3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)), d_p);

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

    std::vector< Node > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)), d_p);
    Node y1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
        d_nine32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)), d_p);

    Node x2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)), d_p);
    Node z2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)), d_p);

    Node y3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)), d_p);
    Node z3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)), d_p);


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

    std::vector< Node > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_eight32)), d_p);
    Node y2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_six32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_seven32)), d_p);

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
      TS_ASSERT (res[d_z] == d_nine32);
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
      TS_ASSERT (res[d_z] == d_nine32);
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

    std::vector< Node > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)), d_p);
    Node y1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_nine32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)), d_p);
    Node x2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)), d_p);
    Node z2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)), d_p);
    Node y3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)), d_p);
    Node z3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)), d_p);

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

    std::vector< Node > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_one32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_one32)), d_p);
    Node y1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_four32, d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_nine32)), d_p);
    Node x2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_five32)), d_p);
    Node z2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_five32)), d_p);
    Node y3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_six32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_nine32)), d_p);
    Node z3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_ten32, d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_one32)), d_p);

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

    std::vector< Node > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 1);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_one32), d_three);
    Node y2 = d_nm->mkNode(kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_one32), d_three);

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

    Node x = mkConcat (d_zero,
        mkConcat (zero, mkExtract (mkConcat (zero, xx), 7, 0)));
    Node y = mkConcat (d_zero,
        mkConcat (zero, mkExtract (mkConcat (zero, yy), 7, 0)));
    Node z = mkConcat (d_zero,
        mkConcat (zero, mkExtract (mkConcat (zero, zz), 7, 0)));
    Node x_mul_one = d_nm->mkNode(kind::BITVECTOR_MULT, x, d_one32);
    Node nine_mul_z = d_nm->mkNode(kind::BITVECTOR_MULT, d_nine32, z);
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

    std::vector< Node > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32, d_nm->mkNode(kind::BITVECTOR_MULT, z, d_two32)), d_p);
    Node y1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_nine32, d_nm->mkNode(kind::BITVECTOR_MULT, z, d_eight32)), d_p);

    Node x2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, y, d_three32)), d_p);
    Node z2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, y, d_seven32)), d_p);

    Node y3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32, d_nm->mkNode(kind::BITVECTOR_MULT, x, d_four32)), d_p);
    Node z3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32, d_nm->mkNode(kind::BITVECTOR_MULT, x, d_six32)), d_p);

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

    Node x = mkConcat (d_zero,
        mkConcat (zero,
          mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, xx), 7, 0)));
    Node y = mkConcat (d_zero,
      mkConcat (zero,
        mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, yy), 7, 0)));
    Node z = mkConcat (d_zero,
      mkConcat (zero,
        mkExtract (d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, zz), 7, 0)));

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

    std::vector< Node > eqs = { eq1, eq2 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::PARTIAL);
    TS_ASSERT (res.size() == 2);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32,
          d_nm->mkNode(kind::BITVECTOR_MULT, z_mul_zz, d_two32)), d_p);
    Node y1 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_nine32,
          d_nm->mkNode(kind::BITVECTOR_MULT, z_mul_zz, d_eight32)), d_p);

    Node x2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32,
          d_nm->mkNode(kind::BITVECTOR_MULT, y_mul_yy, d_three32)), d_p);
    Node z2 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32,
          d_nm->mkNode(kind::BITVECTOR_MULT, y_mul_yy, d_seven32)), d_p);

    Node y3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_three32,
          d_nm->mkNode(kind::BITVECTOR_MULT, x_mul_xx, d_four32)), d_p);
    Node z3 = d_nm->mkNode(kind::BITVECTOR_UREM,
      d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_two32,
          d_nm->mkNode(kind::BITVECTOR_MULT, x_mul_xx, d_six32)), d_p);

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

  void testGaussElimRewriteForUremNotInvalid1 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     * 3x / 2z = 4  modulo 11
     * 2x % 5y = 2
     * y O z = 5
     * ------------------------------------------------------------------- */

    Node n1 = 
        d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL,
          d_nm->mkNode(kind::BITVECTOR_MULT, d_three, d_x),
          d_nm->mkNode(kind::BITVECTOR_MULT, d_two, d_y));
    Node n2 = 
        d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL,
          d_nm->mkNode(kind::BITVECTOR_MULT, d_two, d_x),
          d_nm->mkNode(kind::BITVECTOR_MULT, d_five, d_y));
    Node n3 = mkConcat (d_zero,
        mkExtract(d_nm->mkNode(kind::BITVECTOR_CONCAT, d_y, d_z), 15, 0));

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n1, d_p), d_four);

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n2, d_p), d_two);

    Node eq3 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n3, d_p), d_five);

    std::vector< Node > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::UNIQUE);
    TS_ASSERT (res.size() == 3);

    TS_ASSERT(res[n1] == d_four32);
    TS_ASSERT(res[n2] == d_two32);
    TS_ASSERT(res[n3] == d_five32);
  }

  void testGaussElimRewriteForUremNotInvalid2 ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     * x*y = 4  modulo 11
     * x*y*z = 2
     * 2*x*y + 2*z = 9
     * ------------------------------------------------------------------- */

    Node zero32 = mkZero(32);

    Node x = mkConcat(zero32, d_nm->mkVar("x", d_nm->mkBitVectorType(16)));
    Node y = mkConcat(zero32, d_nm->mkVar("y", d_nm->mkBitVectorType(16)));
    Node z = mkConcat(zero32, d_nm->mkVar("z", d_nm->mkBitVectorType(16)));

    Node n1 = d_nm->mkNode(kind::BITVECTOR_MULT, x, y);
    Node n2 = d_nm->mkNode(kind::BITVECTOR_MULT,
        d_nm->mkNode(kind::BITVECTOR_MULT, x, y), z);
    Node n3 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        d_nm->mkNode(kind::BITVECTOR_MULT,
          d_nm->mkNode(kind::BITVECTOR_MULT, x, y),
          mkConcat (d_zero, d_two)),
        d_nm->mkNode(kind::BITVECTOR_MULT,
          mkConcat (d_zero, d_two), z));

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n1, mkConcat(d_zero, d_p)),
        mkConcat(d_zero, d_four));

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n2, mkConcat(d_zero, d_p)),
        mkConcat(d_zero, d_two));

    Node eq3 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n3, mkConcat(d_zero, d_p)),
        mkConcat(d_zero, d_nine));

    std::vector< Node > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::UNIQUE);
    TS_ASSERT (res.size() == 3);

    TS_ASSERT(res[n1] == mkConst(48, 4));
    TS_ASSERT(res[n2] == mkConst(48, 2));

    Integer twoxy = (res[n1].getConst<BitVector>().getValue()
                     * Integer(2)).euclidianDivideRemainder(Integer(48));
    Integer twoz = (res[z].getConst<BitVector>().getValue()
                     * Integer(2)).euclidianDivideRemainder(Integer(48));
    Integer r = (twoxy + twoz).euclidianDivideRemainder(Integer(11));
    TS_ASSERT(r == Integer(9));
  }

  void testGaussElimRewriteForUremInvalid ()
  {
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::Result ret;

    /* -------------------------------------------------------------------
     * x*y = 4  modulo 11
     * x*y*z = 2
     * 2*x*y = 9
     * ------------------------------------------------------------------- */

    Node zero32 = mkZero(32);

    Node x = mkConcat(zero32, d_nm->mkVar("x", d_nm->mkBitVectorType(16)));
    Node y = mkConcat(zero32, d_nm->mkVar("y", d_nm->mkBitVectorType(16)));
    Node z = mkConcat(zero32, d_nm->mkVar("z", d_nm->mkBitVectorType(16)));

    Node n1 = d_nm->mkNode(kind::BITVECTOR_MULT, x, y);
    Node n2 = d_nm->mkNode(kind::BITVECTOR_MULT,
        d_nm->mkNode(kind::BITVECTOR_MULT, x, y), z);
    Node n3 = d_nm->mkNode(kind::BITVECTOR_MULT,
          d_nm->mkNode(kind::BITVECTOR_MULT, x, y),
          mkConcat (d_zero, d_two));

    Node eq1 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n1, mkConcat(d_zero, d_p)),
        mkConcat(d_zero, d_four));

    Node eq2 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n2, mkConcat(d_zero, d_p)),
        mkConcat(d_zero, d_two));

    Node eq3 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM, n3, mkConcat(d_zero, d_p)),
        mkConcat(d_zero, d_nine));

    std::vector< Node > eqs = { eq1, eq2, eq3 };
    ret = BVGaussElim::gaussElimRewriteForUrem (eqs, res);
    TS_ASSERT (ret == BVGaussElim::Result::NONE);
  }

  void testGaussElimRewriteUnique1 ()
  {
    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */

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

    Node a = d_nm->mkNode(kind::AND, d_nm->mkNode(kind::AND, eq1, eq2), eq3);

    std::vector< Node > ass = { a };
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::gaussElimRewrite (ass);
    Node resx = d_nm->mkNode(kind::EQUAL,
        d_x, d_nm->mkConst< BitVector > (BitVector (32, 3u)));
    Node resy = d_nm->mkNode(kind::EQUAL,
        d_y, d_nm->mkConst< BitVector > (BitVector (32, 4u)));
    Node resz = d_nm->mkNode(kind::EQUAL,
        d_z, d_nm->mkConst< BitVector > (BitVector (32, 9u)));
    TS_ASSERT (ass.size() == 4);
    TS_ASSERT (std::find (ass.begin(), ass.end(), resx) != ass.end()); 
    TS_ASSERT (std::find (ass.begin(), ass.end(), resy) != ass.end()); 
    TS_ASSERT (std::find (ass.begin(), ass.end(), resz) != ass.end()); 
  }

  void testGaussElimRewriteUnique2 ()
  {
    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5        1 0 0   3
     *  2 3 5   8        0 1 0   4
     *  4 0 5   2        0 0 1   9
     *
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  4 6 0   3        0 1 0   2
     * ------------------------------------------------------------------- */

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

    Node y_mul_six = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_six);

    Node eq4 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, y_mul_six),
          d_seven),
        d_four);

    Node eq5 = d_nm->mkNode(kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, y_mul_six),
          d_seven),
        d_three);

    Node a = d_nm->mkNode(kind::AND, d_nm->mkNode(kind::AND, eq1, eq2), eq3);

    std::vector< Node > ass = { a, eq4, eq5 };
    std::unordered_map< Node, Node, NodeHashFunction > res;
    BVGaussElim::gaussElimRewrite (ass);
    Node resx1 = d_nm->mkNode(kind::EQUAL,
        d_x, d_nm->mkConst< BitVector > (BitVector (32, 3u)));
    Node resx2 = d_nm->mkNode(kind::EQUAL,
        d_x, d_nm->mkConst< BitVector > (BitVector (32, 3u)));
    Node resy1 = d_nm->mkNode(kind::EQUAL,
        d_y, d_nm->mkConst< BitVector > (BitVector (32, 4u)));
    Node resy2 = d_nm->mkNode(kind::EQUAL,
        d_y, d_nm->mkConst< BitVector > (BitVector (32, 2u)));
    Node resz = d_nm->mkNode(kind::EQUAL,
        d_z, d_nm->mkConst< BitVector > (BitVector (32, 9u)));
    TS_ASSERT (ass.size() == 8);
    TS_ASSERT (std::find (ass.begin(), ass.end(), resx1) != ass.end()); 
    TS_ASSERT (std::find (ass.begin(), ass.end(), resx2) != ass.end()); 
    TS_ASSERT (std::find (ass.begin(), ass.end(), resy1) != ass.end()); 
    TS_ASSERT (std::find (ass.begin(), ass.end(), resy2) != ass.end()); 
    TS_ASSERT (std::find (ass.begin(), ass.end(), resz) != ass.end()); 
  }

  void testGaussElimRewritePartial ()
  {
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

    std::vector< Node > ass = { eq1, eq2 };
    BVGaussElim::gaussElimRewrite (ass);
    TS_ASSERT (ass.size() == 4);

    Node resx1 = d_nm->mkNode(kind::EQUAL, d_x,
      d_nm->mkNode(kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_seven32,
          d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)),
        d_p));
    Node resy1 = d_nm->mkNode(kind::EQUAL, d_y,
      d_nm->mkNode(kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
          d_nine32,
          d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)),
        d_p));

    Node resx2 = d_nm->mkNode(kind::EQUAL, d_x,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_two32,
            d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)),
          d_p));
    Node resz2 = d_nm->mkNode(kind::EQUAL, d_z,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_three32,
            d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)),
          d_p));

    Node resy3 = d_nm->mkNode(kind::EQUAL, d_y,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_three32,
            d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)),
          d_p));
    Node resz3 = d_nm->mkNode(kind::EQUAL, d_z,
        d_nm->mkNode(kind::BITVECTOR_UREM,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_two32,
            d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)),
          d_p));

    bool fx1 = std::find (ass.begin(), ass.end(), resx1) != ass.end();
    bool fy1 = std::find (ass.begin(), ass.end(), resy1) != ass.end();
    bool fx2 = std::find (ass.begin(), ass.end(), resx2) != ass.end();
    bool fz2 = std::find (ass.begin(), ass.end(), resz2) != ass.end();
    bool fy3 = std::find (ass.begin(), ass.end(), resy3) != ass.end();
    bool fz3 = std::find (ass.begin(), ass.end(), resz3) != ass.end();

    /* result depends on order of variables in matrix */
    TS_ASSERT ((fx1 && fy1) || (fx2 && fz2) || (fy3 && fz3));
  }

  void testGetMinBw1 ()
  {
    Node p = d_nm->mkConst<BitVector> (BitVector(16, 11u));
    TS_ASSERT (BVGaussElim::getMinBwExpr(p) == 4);

    Node p8 = d_nm->mkConst<BitVector> (BitVector(8, 11u));
    Node ext = mkExtract(p, 4, 0);
    Node zextop8 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(8));
    Node zextop32 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(32));
    Node zextop40 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(40));
    Node zext24 = d_nm->mkNode(zextop8, p);
    Node zext48 = d_nm->mkNode(zextop32, p);
    Node zext48_2 = d_nm->mkNode(zextop40, p8);

    TS_ASSERT (BVGaussElim::getMinBwExpr(ext) == 4);
    TS_ASSERT (BVGaussElim::getMinBwExpr(zext24) == 4);
    TS_ASSERT (BVGaussElim::getMinBwExpr(zext48) == 4);
    TS_ASSERT (BVGaussElim::getMinBwExpr(zext48_2) == 4);

    Node mult1 = d_nm->mkNode(kind::BITVECTOR_MULT, ext, ext);
    TS_ASSERT (BVGaussElim::getMinBwExpr(mult1) == 0);

    Node mult2 = d_nm->mkNode(kind::BITVECTOR_MULT, zext24, zext24);
    TS_ASSERT (BVGaussElim::getMinBwExpr(mult2) == 8);

    NodeBuilder<> nbmult3(kind::BITVECTOR_MULT);
    nbmult3 << zext48 << zext48 << zext48;
    Node mult3 = nbmult3;
    TS_ASSERT (BVGaussElim::getMinBwExpr(mult3) == 12);

    NodeBuilder<> nbmult4(kind::BITVECTOR_MULT);
    nbmult4 << zext48 << zext48_2 << zext48;
    Node mult4 = nbmult4;
    TS_ASSERT (BVGaussElim::getMinBwExpr(mult4) == 12);

    Node concat1 = mkConcat(p, zext48);
    TS_ASSERT (BVGaussElim::getMinBwExpr(concat1) == 52);

    Node concat2 = mkConcat(mkZero(16), zext48);
    TS_ASSERT (BVGaussElim::getMinBwExpr(concat2) == 4);

    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, zext48, zext48);
    TS_ASSERT (BVGaussElim::getMinBwExpr(udiv1) == 4);

    Node udiv2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, zext48, zext48_2);
    TS_ASSERT (BVGaussElim::getMinBwExpr(udiv2) == 4);

    Node urem1 = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48, zext48);
    TS_ASSERT (BVGaussElim::getMinBwExpr(urem1) == 4);

    Node urem2 = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48, zext48_2);
    TS_ASSERT (BVGaussElim::getMinBwExpr(urem2) == 4);

    Node urem3 = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48_2, zext48);
    TS_ASSERT (BVGaussElim::getMinBwExpr(urem3) == 4);

    Node add1 = d_nm->mkNode(kind::BITVECTOR_PLUS, ext, ext);
    TS_ASSERT (BVGaussElim::getMinBwExpr(add1) == 5);

    Node add2 = d_nm->mkNode(kind::BITVECTOR_PLUS, zext24, zext24);
    TS_ASSERT (BVGaussElim::getMinBwExpr(add2) == 5);

    NodeBuilder<> nbadd3(kind::BITVECTOR_PLUS);
    nbadd3 << zext48 << zext48 << zext48;
    Node add3 = nbadd3;
    TS_ASSERT (BVGaussElim::getMinBwExpr(add3) == 6);

    NodeBuilder<> nbadd4(kind::BITVECTOR_PLUS);
    nbadd4 << zext48 << zext48_2 << zext48;
    Node add4 = nbadd4;
    TS_ASSERT (BVGaussElim::getMinBwExpr(add4) == 6);

    Node not1 = d_nm->mkNode(kind::BITVECTOR_NOT, zext24);
    TS_ASSERT (BVGaussElim::getMinBwExpr(not1) == 4);
  }

  void testGetMinBw2 ()
  {
    /* ((_ zero_extend 5)
     *     ((_ extract 7 0) ((_ zero_extend 15) d_p)))  */
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop15 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(15));
    Node zext1 = d_nm->mkNode(zextop15, d_p);
    Node ext = mkExtract(zext1, 7, 0);
    Node zext2 = d_nm->mkNode(zextop5, ext);
    TS_ASSERT (BVGaussElim::getMinBwExpr(zext2) == 4);
  }

  void testGetMinBw3 ()
  {
    /* ((_ zero_extend 5)
     *     (bvudiv ((_ extract 4 0) ((_ zero_extend 5) (bvudiv x z)))
     *             ((_ extract 4 0) w)))  */
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, d_p, d_nine);
    Node zext1 = d_nm->mkNode(zextop5, udiv1);
    Node ext1 = mkExtract(zext1, 4, 0);
    Node ext2 = mkExtract(d_two, 4, 0);
    Node udiv2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1, ext2);
    Node zext2 = mkConcat(mkZero(5), udiv2);
    TS_ASSERT (BVGaussElim::getMinBwExpr(zext2) == 4);
  }

  void testGetMinBw4 ()
  {
    /* (bvadd
     *     ((_ zero_extend 5)
     *         (bvudiv ((_ extract 4 0) ((_ zero_extend 5) (bvudiv x z)))
     *                 ((_ extract 4 0) w)))
     *     ((_ zero_extend 7)
     *         (bvudiv ((_ extract 2 0) ((_ zero_extend 5) (bvudiv x z)))
     *                 ((_ extract 2 0) w)))  */
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop7 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(7));

    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, d_p, d_nine);
    Node zext1 = d_nm->mkNode(zextop5, udiv1);

    Node ext1_1 = mkExtract(zext1, 4, 0);
    Node ext2_1 = mkExtract(d_two, 4, 0);
    Node udiv2_1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1_1, ext2_1);
    Node zext2_1 = mkConcat(mkZero(5), udiv2_1);

    Node ext1_2 = mkExtract(zext1, 2, 0);
    Node ext2_2 = mkExtract(d_two, 2, 0);
    Node udiv2_2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1_2, ext2_2);
    Node zext2_2 = d_nm->mkNode(zextop7, udiv2_2);

    Node plus = d_nm->mkNode(kind::BITVECTOR_PLUS, zext2_1, zext2_2);

    TS_ASSERT (BVGaussElim::getMinBwExpr(plus) == 4);
  }

  void testGetMinBw5a ()
  {
    /* (bvadd
     *   (bvadd
     *     (bvadd
     *       (bvadd
     *         (bvadd
     *           (bvadd
     *             (bvadd (bvmul (_ bv86 13)
     *                           ((_ zero_extend 5)
     *                             ((_ extract 7 0) ((_ zero_extend 15) x))))
     *                    (bvmul (_ bv41 13)
     *                           ((_ zero_extend 5)
     *                             ((_ extract 7 0) ((_ zero_extend 15) y)))))
     *             (bvmul (_ bv37 13)
     *                    ((_ zero_extend 5)
     *                      ((_ extract 7 0) ((_ zero_extend 15) z)))))
     *           (bvmul (_ bv170 13)
     *                  ((_ zero_extend 5)
     *                    ((_ extract 7 0) ((_ zero_extend 15) u)))))
     *         (bvmul (_ bv112 13)
     *                ((_ zero_extend 5)
     *                  ((_ extract 7 0) ((_ zero_extend 15) v)))))
     *       (bvmul (_ bv195 13) ((_ zero_extend 5) ((_ extract 15 8) s))))
     *     (bvmul (_ bv124 13) ((_ zero_extend 5) ((_ extract 7 0) s))))
     *   (bvmul (_ bv83 13)
     *          ((_ zero_extend 5) ((_ extract 7 0) ((_ zero_extend 15) w)))))
     */
    Node x = mkVar(1);
    Node y = mkVar(1);
    Node z = mkVar(1);
    Node u = mkVar(1);
    Node v = mkVar(1);
    Node w = mkVar(1);
    Node s = mkVar(16);

    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop15 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(15));

    Node zext15x = d_nm->mkNode(zextop15, x);
    Node zext15y = d_nm->mkNode(zextop15, y);
    Node zext15z = d_nm->mkNode(zextop15, z);
    Node zext15u = d_nm->mkNode(zextop15, u);
    Node zext15v = d_nm->mkNode(zextop15, v);
    Node zext15w = d_nm->mkNode(zextop15, w);

    Node ext7x = mkExtract(zext15x, 7, 0);
    Node ext7y = mkExtract(zext15y, 7, 0);
    Node ext7z = mkExtract(zext15z, 7, 0);
    Node ext7u = mkExtract(zext15u, 7, 0);
    Node ext7v = mkExtract(zext15v, 7, 0);
    Node ext7w = mkExtract(zext15w, 7, 0);
    Node ext7s = mkExtract(s, 7, 0);
    Node ext15s = mkExtract(s, 15, 8);

    Node xx = mkConcat(mkZero(5), ext7x);
    Node yy = mkConcat(mkZero(5), ext7y);
    Node zz = mkConcat(mkZero(5), ext7z);
    Node uu = mkConcat(mkZero(5), ext7u);
    Node vv = mkConcat(mkZero(5), ext7v);
    Node ww = mkConcat(mkZero(5), ext7w);
    Node s7 = mkConcat(mkZero(5), ext7s);
    Node s15 = mkConcat(mkZero(5), ext15s);

    Node plus1 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 86), xx),
        d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 41), yy));
    Node plus2 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus1, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 37), zz));
    Node plus3 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus2, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 170), uu));
    Node plus4 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus3, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 112), uu));
    Node plus5 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus4, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 195), s15));
    Node plus6 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus5, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 124), s7));
    Node plus7 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus6, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(13, 83), ww));

    TS_ASSERT (BVGaussElim::getMinBwExpr(plus7) == 0);
  }

  void testGetMinBw5b ()
  {
    /* (bvadd
     *   (bvadd
     *     (bvadd
     *       (bvadd
     *         (bvadd
     *           (bvadd
     *             (bvadd (bvmul (_ bv86 18)
     *                           ((_ zero_extend 10)
     *                             ((_ extract 7 0) ((_ zero_extend 15) x))))
     *                    (bvmul (_ bv41 18)
     *                           ((_ zero_extend 10)
     *                             ((_ extract 7 0) ((_ zero_extend 15) y)))))
     *             (bvmul (_ bv37 18)
     *                    ((_ zero_extend 10)
     *                      ((_ extract 7 0) ((_ zero_extend 15) z)))))
     *           (bvmul (_ bv170 18)
     *                  ((_ zero_extend 10)
     *                    ((_ extract 7 0) ((_ zero_extend 15) u)))))
     *         (bvmul (_ bv112 18)
     *                ((_ zero_extend 10)
     *                  ((_ extract 7 0) ((_ zero_extend 15) v)))))
     *       (bvmul (_ bv195 18) ((_ zero_extend 10) ((_ extract 15 8) s))))
     *     (bvmul (_ bv124 18) ((_ zero_extend 10) ((_ extract 7 0) s))))
     *   (bvmul (_ bv83 18)
     *          ((_ zero_extend 10) ((_ extract 7 0) ((_ zero_extend 15) w)))))
     */
    Node x = mkVar(1);
    Node y = mkVar(1);
    Node z = mkVar(1);
    Node u = mkVar(1);
    Node v = mkVar(1);
    Node w = mkVar(1);
    Node s = mkVar(16);

    Node zextop15 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(15));

    Node zext15x = d_nm->mkNode(zextop15, x);
    Node zext15y = d_nm->mkNode(zextop15, y);
    Node zext15z = d_nm->mkNode(zextop15, z);
    Node zext15u = d_nm->mkNode(zextop15, u);
    Node zext15v = d_nm->mkNode(zextop15, v);
    Node zext15w = d_nm->mkNode(zextop15, w);

    Node ext7x = mkExtract(zext15x, 7, 0);
    Node ext7y = mkExtract(zext15y, 7, 0);
    Node ext7z = mkExtract(zext15z, 7, 0);
    Node ext7u = mkExtract(zext15u, 7, 0);
    Node ext7v = mkExtract(zext15v, 7, 0);
    Node ext7w = mkExtract(zext15w, 7, 0);
    Node ext7s = mkExtract(s, 7, 0);
    Node ext15s = mkExtract(s, 15, 8);

    Node xx = mkConcat(mkZero(10), ext7x);
    Node yy = mkConcat(mkZero(10), ext7y);
    Node zz = mkConcat(mkZero(10), ext7z);
    Node uu = mkConcat(mkZero(10), ext7u);
    Node vv = mkConcat(mkZero(10), ext7v);
    Node ww = mkConcat(mkZero(10), ext7w);
    Node s7 = mkConcat(mkZero(10), ext7s);
    Node s15 = mkConcat(mkZero(10), ext15s);

    Node plus1 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 86), xx),
        d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 41), yy));
    Node plus2 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus1, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 37), zz));
    Node plus3 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus2, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 170), uu));
    Node plus4 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus3, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 112), uu));
    Node plus5 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus4, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 195), s15));
    Node plus6 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus5, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 124), s7));
    Node plus7 = d_nm->mkNode(kind::BITVECTOR_PLUS,
        plus6, d_nm->mkNode(kind::BITVECTOR_MULT, mkConst(18, 83), ww));

    TS_ASSERT (BVGaussElim::getMinBwExpr(plus7) == 16);
  }

};
