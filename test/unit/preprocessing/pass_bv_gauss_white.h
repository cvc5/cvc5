/*********************                                                        */
/*! \file pass_bv_gauss_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for Gaussian Elimination preprocessing pass.
 **
 ** Unit tests for Gaussian Elimination preprocessing pass.
 **/

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "preprocessing/passes/bv_gauss.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "test_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <vector>

using namespace CVC4;
using namespace CVC4::preprocessing;
using namespace CVC4::preprocessing::passes;
using namespace CVC4::theory;
using namespace CVC4::smt;

static void print_matrix_dbg(std::vector<Integer> &rhs,
                             std::vector<std::vector<Integer>> &lhs)
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

static void testGaussElimX(Integer prime,
                           std::vector<Integer> rhs,
                           std::vector<std::vector<Integer>> lhs,
                           BVGauss::Result expected,
                           std::vector<Integer>* rrhs = nullptr,
                           std::vector<std::vector<Integer>>* rlhs = nullptr)
{
  size_t nrows = lhs.size();
  size_t ncols = lhs[0].size();
  BVGauss::Result ret;
  std::vector<Integer> resrhs = std::vector<Integer>(rhs);
  std::vector<std::vector<Integer>> reslhs =
      std::vector<std::vector<Integer>>(lhs);

  std::cout << "Input: " << std::endl;
  print_matrix_dbg(rhs, lhs);

  ret = BVGauss::gaussElim(prime, resrhs, reslhs);

  std::cout << "BVGauss::Result: "
            << (ret == BVGauss::Result::INVALID
                    ? "INVALID"
                    : (ret == BVGauss::Result::UNIQUE
                           ? "UNIQUE"
                           : (ret == BVGauss::Result::PARTIAL ? "PARTIAL"
                                                              : "NONE")))
            << std::endl;
  print_matrix_dbg(resrhs, reslhs);

  TS_ASSERT_EQUALS(expected, ret);

  if (expected == BVGauss::Result::UNIQUE)
  {
    /* map result value to column index
     * e.g.:
     * 1 0 0 2  -> res = { 2, 0, 3}
     * 0 0 1 3 */
    std::vector<Integer> res = std::vector<Integer>(ncols, Integer(0));
    for (size_t i = 0; i < nrows; ++i)
      for (size_t j = 0; j < ncols; ++j)
      {
        if (reslhs[i][j] == 1)
          res[j] = resrhs[i];
        else
          TS_ASSERT(reslhs[i][j] == 0);
      }

    for (size_t i = 0; i < nrows; ++i)
    {
      Integer tmp = Integer(0);
      for (size_t j = 0; j < ncols; ++j)
        tmp = tmp.modAdd(lhs[i][j].modMultiply(res[j], prime), prime);
      TS_ASSERT(tmp == rhs[i].euclidianDivideRemainder(prime));
    }
  }
  if (rrhs != nullptr && rlhs != nullptr)
  {
    for (size_t i = 0; i < nrows; ++i)
    {
      for (size_t j = 0; j < ncols; ++j)
      {
        TS_ASSERT(reslhs[i][j] == (*rlhs)[i][j]);
      }
      TS_ASSERT(resrhs[i] == (*rrhs)[i]);
    }
  }
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
  TheoryBVGaussWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);
    d_smt->finishInit();

    d_zero = bv::utils::mkZero(16);

    d_p = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 11u)));
    d_x = bv::utils::mkConcat(
        d_zero, d_nm->mkVar("x", d_nm->mkBitVectorType(16)));
    d_y = bv::utils::mkConcat(
        d_zero, d_nm->mkVar("y", d_nm->mkBitVectorType(16)));
    d_z = bv::utils::mkConcat(
        d_zero, d_nm->mkVar("z", d_nm->mkBitVectorType(16)));

    d_one = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 1u)));
    d_two = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 2u)));
    d_three = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 3u)));
    d_four = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 4u)));
    d_five = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 5u)));
    d_six = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 6u)));
    d_seven = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 7u)));
    d_eight = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 8u)));
    d_nine = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 9u)));
    d_ten = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 10u)));
    d_twelve = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 12u)));
    d_eighteen = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 18u)));
    d_twentyfour = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 24u)));
    d_thirty = bv::utils::mkConcat(
        d_zero, d_nm->mkConst<BitVector>(BitVector(16, 30u)));

    d_one32 = d_nm->mkConst<BitVector>(BitVector(32, 1u));
    d_two32 = d_nm->mkConst<BitVector>(BitVector(32, 2u));
    d_three32 = d_nm->mkConst<BitVector>(BitVector(32, 3u));
    d_four32 = d_nm->mkConst<BitVector>(BitVector(32, 4u));
    d_five32 = d_nm->mkConst<BitVector>(BitVector(32, 5u));
    d_six32 = d_nm->mkConst<BitVector>(BitVector(32, 6u));
    d_seven32 = d_nm->mkConst<BitVector>(BitVector(32, 7u));
    d_eight32 = d_nm->mkConst<BitVector>(BitVector(32, 8u));
    d_nine32 = d_nm->mkConst<BitVector>(BitVector(32, 9u));
    d_ten32 = d_nm->mkConst<BitVector>(BitVector(32, 10u));

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

  void tearDown() override
  {
    (void)d_scope;
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

  void testGaussElimMod()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 }
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(2)};
    lhs = {{Integer(1), Integer(1), Integer(1)},
           {Integer(2), Integer(3), Integer(5)},
           {Integer(4), Integer(0), Integer(5)}};
    std::cout << "matrix 0, modulo 0" << std::endl;  // throws
    TS_UTILS_EXPECT_ABORT(BVGauss::gaussElim(Integer(0), rhs, lhs));
    std::cout << "matrix 0, modulo 1" << std::endl;
    testGaussElimX(Integer(1), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 0, modulo 2" << std::endl;
    testGaussElimX(Integer(2), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 0, modulo 3" << std::endl;
    testGaussElimX(Integer(3), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 0, modulo 4" << std::endl;  // no inverse
    testGaussElimX(Integer(4), rhs, lhs, BVGauss::Result::INVALID);
    std::cout << "matrix 0, modulo 5" << std::endl;
    testGaussElimX(Integer(5), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 0, modulo 6" << std::endl;  // no inverse
    testGaussElimX(Integer(6), rhs, lhs, BVGauss::Result::INVALID);
    std::cout << "matrix 0, modulo 7" << std::endl;
    testGaussElimX(Integer(7), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 0, modulo 8" << std::endl;  // no inverse
    testGaussElimX(Integer(8), rhs, lhs, BVGauss::Result::INVALID);
    std::cout << "matrix 0, modulo 9" << std::endl;
    testGaussElimX(Integer(9), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 0, modulo 10" << std::endl;  // no inverse
    testGaussElimX(Integer(10), rhs, lhs, BVGauss::Result::INVALID);
    std::cout << "matrix 0, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimUniqueDone()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs     rhs        lhs    rhs  modulo 17
     *  --^---    ^        --^--    ^
     *  1 0 0    4   -->   1 0 0    4
     *  0 1 0   15         0 1 0   15
     *  0 0 1    3         0 0 1    3
     * ------------------------------------------------------------------- */
    rhs = {Integer(4), Integer(15), Integer(3)};
    lhs = {{Integer(1), Integer(0), Integer(0)},
           {Integer(0), Integer(1), Integer(0)},
           {Integer(0), Integer(0), Integer(1)}};
    std::cout << "matrix 1, modulo 17" << std::endl;
    testGaussElimX(Integer(17), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimUnique()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs     rhs  modulo { 11,17,59 }
     *  --^---    ^
     *  2 4  6   18
     *  4 5  6   24
     *  3 1 -2    4
     * ------------------------------------------------------------------- */
    rhs = {Integer(18), Integer(24), Integer(4)};
    lhs = {{Integer(2), Integer(4), Integer(6)},
           {Integer(4), Integer(5), Integer(6)},
           {Integer(3), Integer(1), Integer(-2)}};
    std::cout << "matrix 2, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 2, modulo 17" << std::endl;
    testGaussElimX(Integer(17), rhs, lhs, BVGauss::Result::UNIQUE);
    std::cout << "matrix 2, modulo 59" << std::endl;
    testGaussElimX(Integer(59), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *      lhs       rhs         lhs     rhs   modulo 11
     *  -----^-----    ^        ---^---    ^
     *  1  1  2   0    1   -->  1 0 0 0    1
     *  2 -1  0   1   -2        0 1 0 0    2
     *  1 -1 -1  -2    4        0 0 1 0   -1
     *  2 -1  2  -1    0        0 0 0 1   -2
     * ------------------------------------------------------------------- */
    rhs = {Integer(1), Integer(-2), Integer(4), Integer(0)};
    lhs = {{Integer(1), Integer(1), Integer(2), Integer(0)},
           {Integer(2), Integer(-1), Integer(0), Integer(1)},
           {Integer(1), Integer(-1), Integer(-1), Integer(-2)},
           {Integer(2), Integer(-1), Integer(2), Integer(-1)}};
    std::cout << "matrix 3, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimUniqueZero1()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  0 4 5   2   -->  1 0 0   4
     *  1 1 1   5        0 1 0   3
     *  3 2 5   8        0 0 1   9
     * ------------------------------------------------------------------- */
    rhs = {Integer(2), Integer(5), Integer(8)};
    lhs = {{Integer(0), Integer(4), Integer(5)},
           {Integer(1), Integer(1), Integer(1)},
           {Integer(3), Integer(2), Integer(5)}};
    std::cout << "matrix 4, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   4
     *  0 4 5   2        0 1 0   3
     *  3 2 5   8        0 0 1   9
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(2), Integer(8)};
    lhs = {{Integer(1), Integer(1), Integer(1)},
           {Integer(0), Integer(4), Integer(5)},
           {Integer(3), Integer(2), Integer(5)}};
    std::cout << "matrix 5, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   4
     *  3 2 5   8        0 1 0   9
     *  0 4 5   2        0 0 1   3
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(2)};
    lhs = {{Integer(1), Integer(1), Integer(1)},
           {Integer(3), Integer(2), Integer(5)},
           {Integer(0), Integer(4), Integer(5)}};
    std::cout << "matrix 6, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimUniqueZero2()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  0 0 5   2        1 0 0   10
     *  1 1 1   5   -->  0 1 0   10
     *  3 2 5   8        0 0 1   7
     * ------------------------------------------------------------------- */
    rhs = {Integer(2), Integer(5), Integer(8)};
    lhs = {{Integer(0), Integer(0), Integer(5)},
           {Integer(1), Integer(1), Integer(1)},
           {Integer(3), Integer(2), Integer(5)}};
    std::cout << "matrix 7, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   10
     *  0 0 5   2        0 1 0   10
     *  3 2 5   8        0 0 1   7
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(2), Integer(8)};
    lhs = {{Integer(1), Integer(1), Integer(1)},
           {Integer(0), Integer(0), Integer(5)},
           {Integer(3), Integer(2), Integer(5)}};
    std::cout << "matrix 8, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 0   10
     *  3 2 5   8        0 1 0   10
     *  0 0 5   2        0 0 1    7
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(2)};
    lhs = {{Integer(1), Integer(1), Integer(1)},
           {Integer(3), Integer(2), Integer(5)},
           {Integer(0), Integer(0), Integer(5)}};
    std::cout << "matrix 9, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimUniqueZero3()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 0 6   4        1 0 0   3
     *  0 0 0   0   -->  0 0 0   0
     *  4 0 6   3        0 0 1   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(4), Integer(0), Integer(3)};
    lhs = {{Integer(2), Integer(0), Integer(6)},
           {Integer(0), Integer(0), Integer(0)},
           {Integer(4), Integer(0), Integer(6)}};
    std::cout << "matrix 10, modulo 7" << std::endl;
    testGaussElimX(Integer(7), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  0 0 0   0   -->  0 0 0   0
     *  4 6 0   3        0 0 1   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(4), Integer(0), Integer(3)};
    lhs = {{Integer(2), Integer(6), Integer(0)},
           {Integer(0), Integer(0), Integer(0)},
           {Integer(4), Integer(6), Integer(0)}};
    std::cout << "matrix 11, modulo 7" << std::endl;
    testGaussElimX(Integer(7), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimUniqueZero4()
  {
    std::vector<Integer> rhs, resrhs;
    std::vector<std::vector<Integer>> lhs, reslhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 0 0   0
     *  0 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(0), Integer(2)};
    lhs = {{Integer(0), Integer(1), Integer(1)},
           {Integer(0), Integer(0), Integer(0)},
           {Integer(0), Integer(0), Integer(5)}};
    std::cout << "matrix 12, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 3 5   8
     *  0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(0)};
    lhs = {{Integer(0), Integer(1), Integer(1)},
           {Integer(0), Integer(3), Integer(5)},
           {Integer(0), Integer(0), Integer(0)}};
    std::cout << "matrix 13, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  0 3 5   8
     *  0 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(0), Integer(8), Integer(2)};
    lhs = {{Integer(0), Integer(0), Integer(0)},
           {Integer(0), Integer(3), Integer(5)},
           {Integer(0), Integer(0), Integer(5)}};
    std::cout << "matrix 14, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  0 0 0   0
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(0), Integer(2)};
    lhs = {{Integer(1), Integer(0), Integer(1)},
           {Integer(0), Integer(0), Integer(0)},
           {Integer(4), Integer(0), Integer(5)}};
    std::cout << "matrix 15, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  2 0 5   8
     *  0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(0)};
    lhs = {{Integer(1), Integer(0), Integer(1)},
           {Integer(2), Integer(0), Integer(5)},
           {Integer(0), Integer(0), Integer(0)}};
    std::cout << "matrix 16, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  2 0 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(0), Integer(8), Integer(2)};
    lhs = {{Integer(0), Integer(0), Integer(0)},
           {Integer(2), Integer(0), Integer(5)},
           {Integer(4), Integer(0), Integer(5)}};
    std::cout << "matrix 17, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  0 0 0   0
     *  4 0 0   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(0), Integer(2)};
    lhs = {{Integer(1), Integer(1), Integer(0)},
           {Integer(0), Integer(0), Integer(0)},
           {Integer(4), Integer(0), Integer(0)}};
    std::cout << "matrix 18, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  2 3 0   8
     *  0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(0)};
    lhs = {{Integer(1), Integer(1), Integer(0)},
           {Integer(2), Integer(3), Integer(0)},
           {Integer(0), Integer(0), Integer(0)}};
    std::cout << "matrix 18, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 0 0   0
     *  2 3 0   8
     *  4 0 0   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(0), Integer(8), Integer(2)};
    lhs = {{Integer(0), Integer(0), Integer(0)},
           {Integer(2), Integer(3), Integer(0)},
           {Integer(4), Integer(0), Integer(0)}};
    std::cout << "matrix 19, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *     lhs    rhs  modulo 2
     *  ----^---   ^
     *  2  4   6   18     0 0 0   0
     *  4  5   6   24  =  0 1 0   0
     *  2  7  12   30     0 1 0   0
     * ------------------------------------------------------------------- */
    rhs = {Integer(18), Integer(24), Integer(30)};
    lhs = {{Integer(2), Integer(4), Integer(6)},
           {Integer(4), Integer(5), Integer(6)},
           {Integer(2), Integer(7), Integer(12)}};
    std::cout << "matrix 20, modulo 2" << std::endl;
    resrhs = {Integer(0), Integer(0), Integer(0)};
    reslhs = {{Integer(0), Integer(1), Integer(0)},
              {Integer(0), Integer(0), Integer(0)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(2), rhs, lhs, BVGauss::Result::UNIQUE, &resrhs, &reslhs);
  }

  void testGaussElimUniquePartial()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 0 6   4        1 0 0   3
     *  4 0 6   3        0 0 1   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(4), Integer(3)};
    lhs = {{Integer(2), Integer(0), Integer(6)},
           {Integer(4), Integer(0), Integer(6)}};
    std::cout << "matrix 21, modulo 7" << std::endl;
    testGaussElimX(Integer(7), rhs, lhs, BVGauss::Result::UNIQUE);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs   modulo 7
     *  --^--   ^        --^--   ^
     *  2 6 0   4        1 0 0   3
     *  4 6 0   3        0 1 0   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(4), Integer(3)};
    lhs = {{Integer(2), Integer(6), Integer(0)},
           {Integer(4), Integer(6), Integer(0)}};
    std::cout << "matrix 22, modulo 7" << std::endl;
    testGaussElimX(Integer(7), rhs, lhs, BVGauss::Result::UNIQUE);
  }

  void testGaussElimNone()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs     rhs       modulo 9
     *  --^---    ^
     *  2 4  6   18   -->  not coprime (no inverse)
     *  4 5  6   24
     *  3 1 -2    4
     * ------------------------------------------------------------------- */
    rhs = {Integer(18), Integer(24), Integer(4)};
    lhs = {{Integer(2), Integer(4), Integer(6)},
           {Integer(4), Integer(5), Integer(6)},
           {Integer(3), Integer(1), Integer(-2)}};
    std::cout << "matrix 23, modulo 9" << std::endl;
    testGaussElimX(Integer(9), rhs, lhs, BVGauss::Result::INVALID);

    /* -------------------------------------------------------------------
     *     lhs    rhs       modulo 59
     *  ----^---   ^
     *  1 -2  -6   12   --> no solution
     *  2  4  12  -17
     *  1 -4 -12   22
     * ------------------------------------------------------------------- */
    rhs = {Integer(12), Integer(-17), Integer(22)};
    lhs = {{Integer(1), Integer(-2), Integer(-6)},
           {Integer(2), Integer(4), Integer(12)},
           {Integer(1), Integer(-4), Integer(-12)}};
    std::cout << "matrix 24, modulo 59" << std::endl;
    testGaussElimX(Integer(59), rhs, lhs, BVGauss::Result::NONE);

    /* -------------------------------------------------------------------
     *     lhs    rhs       modulo 9
     *  ----^---   ^
     *  2  4   6   18   --> not coprime (no inverse)
     *  4  5   6   24
     *  2  7  12   30
     * ------------------------------------------------------------------- */
    rhs = {Integer(18), Integer(24), Integer(30)};
    lhs = {{Integer(2), Integer(4), Integer(6)},
           {Integer(4), Integer(5), Integer(6)},
           {Integer(2), Integer(7), Integer(12)}};
    std::cout << "matrix 25, modulo 9" << std::endl;
    testGaussElimX(Integer(9), rhs, lhs, BVGauss::Result::INVALID);
  }

  void testGaussElimNoneZero()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  0 1 1   5
     *  0 3 5   8
     *  0 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(2)};
    lhs = {{Integer(0), Integer(1), Integer(1)},
           {Integer(0), Integer(3), Integer(5)},
           {Integer(0), Integer(0), Integer(5)}};
    std::cout << "matrix 26, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::NONE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 0 1   5
     *  2 0 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(2)};
    lhs = {{Integer(1), Integer(0), Integer(1)},
           {Integer(2), Integer(0), Integer(5)},
           {Integer(4), Integer(0), Integer(5)}};
    std::cout << "matrix 27, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::NONE);

    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 0   5
     *  2 3 0   8
     *  4 0 0   2
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8), Integer(2)};
    lhs = {{Integer(1), Integer(1), Integer(0)},
           {Integer(2), Integer(3), Integer(0)},
           {Integer(4), Integer(0), Integer(0)}};
    std::cout << "matrix 28, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::NONE);
  }

  void testGaussElimPartial1()
  {
    std::vector<Integer> rhs, resrhs;
    std::vector<std::vector<Integer>> lhs, reslhs;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */
    rhs = {Integer(7), Integer(9)};
    lhs = {{Integer(1), Integer(0), Integer(9)},
           {Integer(0), Integer(1), Integer(3)}};
    std::cout << "matrix 29, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::PARTIAL);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 3 0   7   -->  1 3 0   7
     *  0 0 1   9        0 0 1   9
     * ------------------------------------------------------------------- */
    rhs = {Integer(7), Integer(9)};
    lhs = {{Integer(1), Integer(3), Integer(0)},
           {Integer(0), Integer(0), Integer(1)}};
    std::cout << "matrix 30, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::PARTIAL);

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 9   7
     *  2 3 5   8        0 1 3   9
     * ------------------------------------------------------------------- */
    rhs = {Integer(5), Integer(8)};
    lhs = {{Integer(1), Integer(1), Integer(1)},
           {Integer(2), Integer(3), Integer(5)}};
    std::cout << "matrix 31, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::PARTIAL);

    /* -------------------------------------------------------------------
     *     lhs    rhs  modulo { 3, 5, 7, 11, 17, 31, 59 }
     *  ----^---   ^
     *  2  4   6   18
     *  4  5   6   24
     *  2  7  12   30
     * ------------------------------------------------------------------- */
    rhs = {Integer(18), Integer(24), Integer(30)};
    lhs = {{Integer(2), Integer(4), Integer(6)},
           {Integer(4), Integer(5), Integer(6)},
           {Integer(2), Integer(7), Integer(12)}};
    std::cout << "matrix 32, modulo 3" << std::endl;
    resrhs = {Integer(0), Integer(0), Integer(0)};
    reslhs = {{Integer(1), Integer(2), Integer(0)},
              {Integer(0), Integer(0), Integer(0)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(3), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);
    resrhs = {Integer(1), Integer(4), Integer(0)};
    std::cout << "matrix 32, modulo 5" << std::endl;
    reslhs = {{Integer(1), Integer(0), Integer(4)},
              {Integer(0), Integer(1), Integer(2)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(5), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 7" << std::endl;
    reslhs = {{Integer(1), Integer(0), Integer(6)},
              {Integer(0), Integer(1), Integer(2)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(7), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 11" << std::endl;
    reslhs = {{Integer(1), Integer(0), Integer(10)},
              {Integer(0), Integer(1), Integer(2)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(11), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 17" << std::endl;
    reslhs = {{Integer(1), Integer(0), Integer(16)},
              {Integer(0), Integer(1), Integer(2)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(17), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);
    std::cout << "matrix 32, modulo 59" << std::endl;
    reslhs = {{Integer(1), Integer(0), Integer(58)},
              {Integer(0), Integer(1), Integer(2)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(59), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);

    /* -------------------------------------------------------------------
     *     lhs    rhs        lhs   rhs   modulo 3
     *  ----^---   ^        --^--   ^
     *   4  6 2   18   -->  1 0 2   0
     *   5  6 4   24        0 0 0   0
     *   7 12 2   30        0 0 0   0
     * ------------------------------------------------------------------- */
    rhs = {Integer(18), Integer(24), Integer(30)};
    lhs = {{Integer(4), Integer(6), Integer(2)},
           {Integer(5), Integer(6), Integer(4)},
           {Integer(7), Integer(12), Integer(2)}};
    std::cout << "matrix 33, modulo 3" << std::endl;
    resrhs = {Integer(0), Integer(0), Integer(0)};
    reslhs = {{Integer(1), Integer(0), Integer(2)},
              {Integer(0), Integer(0), Integer(0)},
              {Integer(0), Integer(0), Integer(0)}};
    testGaussElimX(
        Integer(3), rhs, lhs, BVGauss::Result::PARTIAL, &resrhs, &reslhs);
  }

  void testGaussElimPartial2()
  {
    std::vector<Integer> rhs;
    std::vector<std::vector<Integer>> lhs;

    /* -------------------------------------------------------------------
     *    lhs    rhs  -->    lhs    rhs  modulo 11
     *  ---^---   ^        ---^---   ^
     *  x y z w            x y z w
     *  1 2 0 6   2        1 2 0 0   1 
     *  0 0 2 2   2        0 0 1 0   10
     *  0 0 0 1   2        0 0 0 1   2 
     * ------------------------------------------------------------------- */
    rhs = {Integer(2), Integer(2), Integer(2)};
    lhs = {{Integer(1), Integer(2), Integer(6), Integer(0)},
           {Integer(0), Integer(0), Integer(2), Integer(2)},
           {Integer(0), Integer(0), Integer(1), Integer(0)}};
    std::cout << "matrix 34, modulo 11" << std::endl;
    testGaussElimX(Integer(11), rhs, lhs, BVGauss::Result::PARTIAL);
  }
  void testGaussElimRewriteForUremUnique1()
  {
    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y_mul_one),
                d_z_mul_one),
            d_p),
        d_five);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_three),
                d_z_mul_five),
            d_p),
        d_eight);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_z_mul_five),
            d_p),
        d_two);

    std::vector<Node> eqs = {eq1, eq2, eq3};
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::UNIQUE);
    TS_ASSERT(res.size() == 3);
    TS_ASSERT(res[d_x] == d_three32);
    TS_ASSERT(res[d_y] == d_four32);
    TS_ASSERT(res[d_z] == d_nine32);
  }

  void testGaussElimRewriteForUremUnique2()
  {
    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */

    Node zextop6 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(6));

    Node p = d_nm->mkNode(
        zextop6,
        bv::utils::mkConcat(bv::utils::mkZero(6),
                            d_nm->mkNode(kind::BITVECTOR_PLUS,
                                         bv::utils::mkConst(20, 7),
                                         bv::utils::mkConst(20, 4))));

    Node x_mul_one =
        d_nm->mkNode(kind::BITVECTOR_MULT,
                     d_nm->mkNode(kind::BITVECTOR_SUB, d_five, d_four),
                     d_x);
    Node y_mul_one =
        d_nm->mkNode(kind::BITVECTOR_MULT,
                     d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, d_one, d_five),
                     d_y);
    Node z_mul_one =
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkOne(32), d_z);

    Node x_mul_two = d_nm->mkNode(
        kind::BITVECTOR_MULT,
        d_nm->mkNode(
            kind::BITVECTOR_SHL, bv::utils::mkOne(32), bv::utils::mkOne(32)),
        d_x);
    Node y_mul_three = d_nm->mkNode(kind::BITVECTOR_MULT,
                                    d_nm->mkNode(kind::BITVECTOR_LSHR,
                                                 bv::utils::mkOnes(32),
                                                 bv::utils::mkConst(32, 30)),
                                    d_y);
    Node z_mul_five = d_nm->mkNode(kind::BITVECTOR_MULT,
        bv::utils::mkExtract(
          d_nm->mkNode(
            zextop6, d_nm->mkNode(kind::BITVECTOR_PLUS, d_three, d_two)),
          31, 0),
        d_z);

    Node x_mul_four = d_nm->mkNode(kind::BITVECTOR_MULT,
        d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL,
          d_nm->mkNode(kind::BITVECTOR_PLUS,
            d_nm->mkNode(kind::BITVECTOR_MULT,
             bv::utils::mkConst(32, 4),
             bv::utils::mkConst(32, 5)),
           bv::utils::mkConst(32, 4)),
         bv::utils::mkConst(32, 6)),
        d_x);

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS,
                  x_mul_one,
                  y_mul_one),
                z_mul_one),
            p),
        d_five);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, x_mul_two, y_mul_three),
                z_mul_five),
            p),
        d_eight);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, x_mul_four, z_mul_five),
            d_p),
        d_two);

    std::vector<Node> eqs = {eq1, eq2, eq3};
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::UNIQUE);
    TS_ASSERT(res.size() == 3);
    TS_ASSERT(res[d_x] == d_three32);
    TS_ASSERT(res[d_y] == d_four32);
    TS_ASSERT(res[d_z] == d_nine32);
  }

  void testGaussElimRewriteForUremPartial1()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_z_mul_nine),
            d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_y_mul_one, d_z_mul_three),
            d_p),
        d_nine);

    std::vector<Node> eqs = {eq1, eq2};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_seven32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)),
        d_p);
    Node y1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_nine32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)),
        d_p);

    Node x2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)),
        d_p);
    Node z2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)),
        d_p);

    Node y3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)),
        d_p);
    Node z3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
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
      TS_ASSERT(res[d_y] == y3);
      TS_ASSERT(res[d_z] == z3);
    }
    else if (res.find(d_y) == res.end())
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
      TS_ASSERT(res[d_x] == x2);
      TS_ASSERT(res[d_z] == z2);
    }
    else
    {
      TS_ASSERT(res.find(d_z) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT(res[d_x] == x1);
      TS_ASSERT(res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial1a()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
                     d_nm->mkNode(kind::BITVECTOR_PLUS, d_x, d_z_mul_nine),
                     d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
                     d_nm->mkNode(kind::BITVECTOR_PLUS, d_y, d_z_mul_three),
                     d_p),
        d_nine);

    std::vector<Node> eqs = {eq1, eq2};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_seven32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)),
        d_p);
    Node y1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_nine32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)),
        d_p);

    Node x2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)),
        d_p);
    Node z2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)),
        d_p);

    Node y3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)),
        d_p);
    Node z3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
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
      TS_ASSERT(res[d_y] == y3);
      TS_ASSERT(res[d_z] == z3);
    }
    else if (res.find(d_y) == res.end())
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
      TS_ASSERT(res[d_x] == x2);
      TS_ASSERT(res[d_z] == z2);
    }
    else
    {
      TS_ASSERT(res.find(d_z) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT(res[d_x] == x1);
      TS_ASSERT(res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial2()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 3 0   7   -->  1 3 0   7
     *  0 0 1   9        0 0 1   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y_mul_three),
            d_p),
        d_seven);

    Node eq2 =
        d_nm->mkNode(kind::EQUAL,
                     d_nm->mkNode(kind::BITVECTOR_UREM, d_z_mul_one, d_p),
                     d_nine);

    std::vector<Node> eqs = {eq1, eq2};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_seven32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_eight32)),
        d_p);
    Node y2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_six32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_seven32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
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
      TS_ASSERT(res[d_y] == y2);
      TS_ASSERT(res[d_z] == d_nine32);
    }
    else if (res.find(d_y) == res.end())
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
      TS_ASSERT(res[d_x] == x1);
      TS_ASSERT(res[d_z] == d_nine32);
    }
    else
    {
      TS_ASSERT(false);
    }
  }

  void testGaussElimRewriteForUremPartial3()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 1 1   5   -->  1 0 9   7
     *  2 3 5   8        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y),
                         d_z_mul_one),
            d_p),
        d_five);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_three),
                d_z_mul_five),
            d_p),
        d_eight);

    std::vector<Node> eqs = {eq1, eq2};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_seven32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)),
        d_p);
    Node y1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_nine32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)),
        d_p);
    Node x2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)),
        d_p);
    Node z2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)),
        d_p);
    Node y3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)),
        d_p);
    Node z3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
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
      TS_ASSERT(res[d_y] == y3);
      TS_ASSERT(res[d_z] == z3);
    }
    else if (res.find(d_y) == res.end())
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
      TS_ASSERT(res[d_x] == x2);
      TS_ASSERT(res[d_z] == z2);
    }
    else
    {
      TS_ASSERT(res.find(d_z) == res.end());
      /*
       *  x y z           x y z
       *  1 1 1  5   -->  1 0 9  7
       *  2 3 5  8        0 1 3  9
       *
       *  y x z           y x z
       *  1 1 1  5   -->  1 0 3  9
       *  3 2 5  8        0 1 9  7
       */
      TS_ASSERT(res[d_x] == x1);
      TS_ASSERT(res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial4()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *     lhs    rhs          lhs    rhs  modulo 11
     *  ----^---   ^         ---^---   ^
     *  2  4   6   18   -->  1 0 10    1
     *  4  5   6   24        0 1  2    4
     *  2  7  12   30        0 0  0    0
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_four),
                d_z_mul_six),
            d_p),
        d_eighteen);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_y_mul_five),
                d_z_mul_six),
            d_p),
        d_twentyfour);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_seven),
                d_z_mul_twelve),
            d_p),
        d_thirty);

    std::vector<Node> eqs = {eq1, eq2, eq3};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_one32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_one32)),
        d_p);
    Node y1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_four32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_nine32)),
        d_p);
    Node x2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_five32)),
        d_p);
    Node z2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_five32)),
        d_p);
    Node y3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_six32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_nine32)),
        d_p);
    Node z3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_ten32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_one32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
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
      TS_ASSERT(res[d_y] == y3);
      TS_ASSERT(res[d_z] == z3);
    }
    else if (res.find(d_y) == res.end())
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
      TS_ASSERT(res[d_x] == x2);
      TS_ASSERT(res[d_z] == z2);
    }
    else
    {
      TS_ASSERT(res.find(d_z) == res.end());
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
      TS_ASSERT(res[d_x] == x1);
      TS_ASSERT(res[d_y] == y1);
    }
  }

  void testGaussElimRewriteForUremPartial5()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *     lhs    rhs         lhs   rhs  modulo 3
     *  ----^---   ^         --^--   ^
     *  2  4   6   18   -->  1 2 0   0
     *  4  5   6   24        0 0 0   0
     *  2  7  12   30        0 0 0   0
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_four),
                d_z_mul_six),
            d_three),
        d_eighteen);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_y_mul_five),
                d_z_mul_six),
            d_three),
        d_twentyfour);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_seven),
                d_z_mul_twelve),
            d_three),
        d_thirty);

    std::vector<Node> eqs = {eq1, eq2, eq3};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 1);

    Node x1 = d_nm->mkNode(kind::BITVECTOR_UREM,
                           d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_one32),
                           d_three);
    Node y2 = d_nm->mkNode(kind::BITVECTOR_UREM,
                           d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_one32),
                           d_three);

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
    {
      /*
       *  y x  z           y x z
       *  4 2  6  18  -->  1 2 0 0
       *  5 4  6  24       0 0 0 0
       *  7 2 12  30       0 0 0 0
       *
       *  y  z x            y z x
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
      TS_ASSERT(res[d_y] == y2);
    }
    else if (res.find(d_y) == res.end())
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
      TS_ASSERT(res[d_x] == x1);
    }
    else
    {
      TS_ASSERT(false);
    }
  }

  void testGaussElimRewriteForUremPartial6()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *    lhs    rhs  -->    lhs    rhs  modulo 11
     *  ---^---   ^        ---^---   ^
     *  x y z w            x y z w
     *  1 2 0 6   2        1 2 0 6   2
     *  0 0 2 2   2        0 0 1 1   1
     *  0 0 0 1   2        0 0 0 1   2
     * ------------------------------------------------------------------- */

    Node y_mul_two = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_two);
    Node z_mul_two = d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two);
    Node w = bv::utils::mkConcat(
        d_zero, d_nm->mkVar("w", d_nm->mkBitVectorType(16)));
    Node w_mul_six = d_nm->mkNode(kind::BITVECTOR_MULT, w, d_six);
    Node w_mul_two = d_nm->mkNode(kind::BITVECTOR_MULT, w, d_two);

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                  d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, y_mul_two),
                  w_mul_six),
            d_p),
        d_two);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, z_mul_two, w_mul_two),
            d_p),
        d_two);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, w, d_p),
        d_two);

    std::vector<Node> eqs = {eq1, eq2, eq3};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 3);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_one32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_nine32)),
        d_p);
    Node z1 = d_ten32;
    Node w1 = d_two32;

    Node y2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_six32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_five32)),
        d_p);
    Node z2 = d_ten32;
    Node w2 = d_two32;

    /* result depends on order of variables in matrix */
    if (res.find(d_x) == res.end())
    {
      TS_ASSERT(res[d_y] == y2);
      TS_ASSERT(res[d_z] == z2);
      TS_ASSERT(res[w] == w2);
    }
    else if (res.find(d_y) == res.end())
    {
      TS_ASSERT(res[d_x] == x1);
      TS_ASSERT(res[d_z] == z1);
      TS_ASSERT(res[w] == w1);
    }
    else
    {
      TS_ASSERT(false);
    }
  }

  void testGaussElimRewriteForUremWithExprPartial()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node zero = bv::utils::mkZero(8);
    Node xx = d_nm->mkVar("xx", d_nm->mkBitVectorType(8));
    Node yy = d_nm->mkVar("yy", d_nm->mkBitVectorType(8));
    Node zz = d_nm->mkVar("zz", d_nm->mkBitVectorType(8));

    Node x = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkConcat(
            zero, bv::utils::mkExtract(bv::utils::mkConcat(zero, xx), 7, 0)));
    Node y = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkConcat(
            zero, bv::utils::mkExtract(bv::utils::mkConcat(zero, yy), 7, 0)));
    Node z = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkConcat(
            zero, bv::utils::mkExtract(bv::utils::mkConcat(zero, zz), 7, 0)));

    Node x_mul_one = d_nm->mkNode(kind::BITVECTOR_MULT, x, d_one32);
    Node nine_mul_z = d_nm->mkNode(kind::BITVECTOR_MULT, d_nine32, z);
    Node one_mul_y = d_nm->mkNode(kind::BITVECTOR_MULT, d_one, y);
    Node z_mul_three = d_nm->mkNode(kind::BITVECTOR_MULT, z, d_three);

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
                     d_nm->mkNode(kind::BITVECTOR_PLUS, x_mul_one, nine_mul_z),
                     d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
                     d_nm->mkNode(kind::BITVECTOR_PLUS, one_mul_y, z_mul_three),
                     d_p),
        d_nine);

    std::vector<Node> eqs = {eq1, eq2};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    x = Rewriter::rewrite(x);
    y = Rewriter::rewrite(y);
    z = Rewriter::rewrite(z);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_seven32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, z, d_two32)),
        d_p);
    Node y1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_nine32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, z, d_eight32)),
        d_p);

    Node x2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, y, d_three32)),
        d_p);
    Node z2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, y, d_seven32)),
        d_p);

    Node y3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, x, d_four32)),
        d_p);
    Node z3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, x, d_six32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(x) == res.end())
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
      TS_ASSERT(res[Rewriter::rewrite(y)] == y3);
      TS_ASSERT(res[Rewriter::rewrite(z)] == z3);
    }
    else if (res.find(y) == res.end())
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
      TS_ASSERT(res[x] == x2);
      TS_ASSERT(res[z] == z2);
    }
    else
    {
      TS_ASSERT(res.find(z) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT(res[x] == x1);
      TS_ASSERT(res[y] == y1);
    }
  }

  void testGaussElimRewriteForUremNAryPartial()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node zero = bv::utils::mkZero(8);
    Node xx = d_nm->mkVar("xx", d_nm->mkBitVectorType(8));
    Node yy = d_nm->mkVar("yy", d_nm->mkBitVectorType(8));
    Node zz = d_nm->mkVar("zz", d_nm->mkBitVectorType(8));

    Node x = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkConcat(
            zero,
            bv::utils::mkExtract(
                d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, xx), 7, 0)));
    Node y = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkConcat(
            zero,
            bv::utils::mkExtract(
                d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, yy), 7, 0)));
    Node z = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkConcat(
            zero,
            bv::utils::mkExtract(
                d_nm->mkNode(kind::BITVECTOR_CONCAT, zero, zz), 7, 0)));

    NodeBuilder<> nbx(d_nm, kind::BITVECTOR_MULT);
    nbx << d_x << d_one << x;
    Node x_mul_one_mul_xx = nbx.constructNode();
    NodeBuilder<> nby(d_nm, kind::BITVECTOR_MULT);
    nby << d_y << y << d_one;
    Node y_mul_yy_mul_one = nby.constructNode();
    NodeBuilder<> nbz(d_nm, kind::BITVECTOR_MULT);
    nbz << d_three << d_z << z;
    Node three_mul_z_mul_zz = nbz.constructNode();
    NodeBuilder<> nbz2(d_nm, kind::BITVECTOR_MULT);
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

    std::vector<Node> eqs = {eq1, eq2};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::PARTIAL);
    TS_ASSERT(res.size() == 2);

    x_mul_xx = Rewriter::rewrite(x_mul_xx);
    y_mul_yy = Rewriter::rewrite(y_mul_yy);
    z_mul_zz = Rewriter::rewrite(z_mul_zz);

    Node x1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_seven32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, z_mul_zz, d_two32)),
        d_p);
    Node y1 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_nine32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, z_mul_zz, d_eight32)),
        d_p);

    Node x2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, y_mul_yy, d_three32)),
        d_p);
    Node z2 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, y_mul_yy, d_seven32)),
        d_p);

    Node y3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_three32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, x_mul_xx, d_four32)),
        d_p);
    Node z3 = d_nm->mkNode(
        kind::BITVECTOR_UREM,
        d_nm->mkNode(kind::BITVECTOR_PLUS,
                     d_two32,
                     d_nm->mkNode(kind::BITVECTOR_MULT, x_mul_xx, d_six32)),
        d_p);

    /* result depends on order of variables in matrix */
    if (res.find(x_mul_xx) == res.end())
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
      TS_ASSERT(res[y_mul_yy] == y3);
      TS_ASSERT(res[z_mul_zz] == z3);
    }
    else if (res.find(y_mul_yy) == res.end())
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
      TS_ASSERT(res[x_mul_xx] == x2);
      TS_ASSERT(res[z_mul_zz] == z2);
    }
    else
    {
      TS_ASSERT(res.find(z_mul_zz) == res.end());
      /*
       *  x y z           x y z
       *  1 0 9  7   -->  1 0 9  7
       *  0 1 3  9        0 1 3  9
       *
       *  y x z           y x z
       *  0 1 9  7   -->  1 0 3  9
       *  1 0 3  9        0 1 9  7
       */
      TS_ASSERT(res[x_mul_xx] == x1);
      TS_ASSERT(res[y_mul_yy] == y1);
    }
  }

  void testGaussElimRewriteForUremNotInvalid1()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     * 3x / 2z = 4  modulo 11
     * 2x % 5y = 2
     * y O z = 5
     * ------------------------------------------------------------------- */

    Node n1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL,
                           d_nm->mkNode(kind::BITVECTOR_MULT, d_three, d_x),
                           d_nm->mkNode(kind::BITVECTOR_MULT, d_two, d_y));
    Node n2 = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL,
                           d_nm->mkNode(kind::BITVECTOR_MULT, d_two, d_x),
                           d_nm->mkNode(kind::BITVECTOR_MULT, d_five, d_y));

    Node n3 = bv::utils::mkConcat(
        d_zero,
        bv::utils::mkExtract(
            d_nm->mkNode(kind::BITVECTOR_CONCAT, d_y, d_z), 15, 0));

    Node eq1 = d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::BITVECTOR_UREM, n1, d_p), d_four);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::BITVECTOR_UREM, n2, d_p), d_two);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL, d_nm->mkNode(kind::BITVECTOR_UREM, n3, d_p), d_five);

    std::vector<Node> eqs = {eq1, eq2, eq3};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::UNIQUE);
    TS_ASSERT(res.size() == 3);

    TS_ASSERT(res[n1] == d_four32);
    TS_ASSERT(res[n2] == d_two32);
    TS_ASSERT(res[n3] == d_five32);
  }

  void testGaussElimRewriteForUremNotInvalid2()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     * x*y = 4  modulo 11
     * x*y*z = 2
     * 2*x*y + 2*z = 9
     * ------------------------------------------------------------------- */

    Node zero32 = bv::utils::mkZero(32);

    Node x = bv::utils::mkConcat(zero32,
                                 d_nm->mkVar("x", d_nm->mkBitVectorType(16)));
    Node y = bv::utils::mkConcat(zero32,
                                 d_nm->mkVar("y", d_nm->mkBitVectorType(16)));
    Node z = bv::utils::mkConcat(zero32,
                                 d_nm->mkVar("z", d_nm->mkBitVectorType(16)));

    Node n1 = d_nm->mkNode(kind::BITVECTOR_MULT, x, y);
    Node n2 = d_nm->mkNode(
        kind::BITVECTOR_MULT, d_nm->mkNode(kind::BITVECTOR_MULT, x, y), z);
    Node n3 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        d_nm->mkNode(kind::BITVECTOR_MULT,
                     d_nm->mkNode(kind::BITVECTOR_MULT, x, y),
                     bv::utils::mkConcat(d_zero, d_two)),
        d_nm->mkNode(
            kind::BITVECTOR_MULT, bv::utils::mkConcat(d_zero, d_two), z));

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, n1, bv::utils::mkConcat(d_zero, d_p)),
        bv::utils::mkConcat(d_zero, d_four));

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, n2, bv::utils::mkConcat(d_zero, d_p)),
        bv::utils::mkConcat(d_zero, d_two));

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, n3, bv::utils::mkConcat(d_zero, d_p)),
        bv::utils::mkConcat(d_zero, d_nine));

    std::vector<Node> eqs = {eq1, eq2, eq3};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::UNIQUE);
    TS_ASSERT(res.size() == 3);

    n1 = Rewriter::rewrite(n1);
    n2 = Rewriter::rewrite(n2);
    z = Rewriter::rewrite(z);

    TS_ASSERT(res[n1] ==bv::utils::mkConst(48, 4));
    TS_ASSERT(res[n2] ==bv::utils::mkConst(48, 2));

    Integer twoxy = (res[n1].getConst<BitVector>().getValue() * Integer(2))
                        .euclidianDivideRemainder(Integer(48));
    Integer twoz = (res[z].getConst<BitVector>().getValue() * Integer(2))
                       .euclidianDivideRemainder(Integer(48));
    Integer r = (twoxy + twoz).euclidianDivideRemainder(Integer(11));
    TS_ASSERT(r == Integer(9));
  }

  void testGaussElimRewriteForUremInvalid()
  {
    std::unordered_map<Node, Node, NodeHashFunction> res;
    BVGauss::Result ret;

    /* -------------------------------------------------------------------
     * x*y = 4  modulo 11
     * x*y*z = 2
     * 2*x*y = 9
     * ------------------------------------------------------------------- */

    Node zero32 = bv::utils::mkZero(32);

    Node x = bv::utils::mkConcat(zero32,
                                 d_nm->mkVar("x", d_nm->mkBitVectorType(16)));
    Node y = bv::utils::mkConcat(zero32,
                                 d_nm->mkVar("y", d_nm->mkBitVectorType(16)));
    Node z = bv::utils::mkConcat(zero32,
                                 d_nm->mkVar("z", d_nm->mkBitVectorType(16)));

    Node n1 = d_nm->mkNode(kind::BITVECTOR_MULT, x, y);
    Node n2 = d_nm->mkNode(
        kind::BITVECTOR_MULT, d_nm->mkNode(kind::BITVECTOR_MULT, x, y), z);
    Node n3 = d_nm->mkNode(kind::BITVECTOR_MULT,
                           d_nm->mkNode(kind::BITVECTOR_MULT, x, y),
                           bv::utils::mkConcat(d_zero, d_two));

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, n1, bv::utils::mkConcat(d_zero, d_p)),
        bv::utils::mkConcat(d_zero, d_four));

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, n2, bv::utils::mkConcat(d_zero, d_p)),
        bv::utils::mkConcat(d_zero, d_two));

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM, n3, bv::utils::mkConcat(d_zero, d_p)),
        bv::utils::mkConcat(d_zero, d_nine));

    std::vector<Node> eqs = {eq1, eq2, eq3};
    ret = BVGauss::gaussElimRewriteForUrem(eqs, res);
    TS_ASSERT(ret == BVGauss::Result::INVALID);
  }

  void testGaussElimRewriteUnique1()
  {
    /* -------------------------------------------------------------------
     *   lhs   rhs  modulo 11
     *  --^--   ^
     *  1 1 1   5
     *  2 3 5   8
     *  4 0 5   2
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y_mul_one),
                d_z_mul_one),
            d_p),
        d_five);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_three),
                d_z_mul_five),
            d_p),
        d_eight);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_z_mul_five),
            d_p),
        d_two);

    Node a = d_nm->mkNode(kind::AND, d_nm->mkNode(kind::AND, eq1, eq2), eq3);

    AssertionPipeline apipe;
    apipe.push_back(a);
    passes::BVGauss bgauss(nullptr, "bv-gauss-unit");
    std::unordered_map<Node, Node, NodeHashFunction> res;
    PreprocessingPassResult pres = bgauss.applyInternal(&apipe);
    TS_ASSERT (pres == PreprocessingPassResult::NO_CONFLICT);
    Node resx = d_nm->mkNode(
        kind::EQUAL, d_x, d_nm->mkConst<BitVector>(BitVector(32, 3u)));
    Node resy = d_nm->mkNode(
        kind::EQUAL, d_y, d_nm->mkConst<BitVector>(BitVector(32, 4u)));
    Node resz = d_nm->mkNode(
        kind::EQUAL, d_z, d_nm->mkConst<BitVector>(BitVector(32, 9u)));
    TS_ASSERT(apipe.size() == 4);
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resx) != apipe.end());
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resy) != apipe.end());
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resz) != apipe.end());
  }

  void testGaussElimRewriteUnique2()
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

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_y_mul_one),
                d_z_mul_one),
            d_p),
        d_five);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(
                kind::BITVECTOR_PLUS,
                d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, d_y_mul_three),
                d_z_mul_five),
            d_p),
        d_eight);

    Node eq3 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, d_z_mul_five),
            d_p),
        d_two);

    Node y_mul_six = d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_six);

    Node eq4 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(kind::BITVECTOR_UREM,
                     d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_two, y_mul_six),
                     d_seven),
        d_four);

    Node eq5 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_four, y_mul_six),
            d_seven),
        d_three);

    Node a = d_nm->mkNode(kind::AND, d_nm->mkNode(kind::AND, eq1, eq2), eq3);

    AssertionPipeline apipe;
    apipe.push_back(a);
    apipe.push_back(eq4);
    apipe.push_back(eq5);
    passes::BVGauss bgauss(nullptr, "bv-gauss-unit");
    std::unordered_map<Node, Node, NodeHashFunction> res;
    PreprocessingPassResult pres = bgauss.applyInternal(&apipe);
    TS_ASSERT (pres == PreprocessingPassResult::NO_CONFLICT);
    Node resx1 = d_nm->mkNode(
        kind::EQUAL, d_x, d_nm->mkConst<BitVector>(BitVector(32, 3u)));
    Node resx2 = d_nm->mkNode(
        kind::EQUAL, d_x, d_nm->mkConst<BitVector>(BitVector(32, 3u)));
    Node resy1 = d_nm->mkNode(
        kind::EQUAL, d_y, d_nm->mkConst<BitVector>(BitVector(32, 4u)));
    Node resy2 = d_nm->mkNode(
        kind::EQUAL, d_y, d_nm->mkConst<BitVector>(BitVector(32, 2u)));
    Node resz = d_nm->mkNode(
        kind::EQUAL, d_z, d_nm->mkConst<BitVector>(BitVector(32, 9u)));
    TS_ASSERT(apipe.size() == 8);
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resx1) != apipe.end());
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resx2) != apipe.end());
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resy1) != apipe.end());
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resy2) != apipe.end());
    TS_ASSERT(std::find(apipe.begin(), apipe.end(), resz) != apipe.end());
  }

  void testGaussElimRewritePartial()
  {
    /* -------------------------------------------------------------------
     *   lhs   rhs        lhs   rhs  modulo 11
     *  --^--   ^        --^--   ^
     *  1 0 9   7   -->  1 0 9   7
     *  0 1 3   9        0 1 3   9
     * ------------------------------------------------------------------- */

    Node eq1 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_x_mul_one, d_z_mul_nine),
            d_p),
        d_seven);

    Node eq2 = d_nm->mkNode(
        kind::EQUAL,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS, d_y_mul_one, d_z_mul_three),
            d_p),
        d_nine);

    AssertionPipeline apipe;
    apipe.push_back(eq1);
    apipe.push_back(eq2);
    passes::BVGauss bgauss(nullptr, "bv-gauss-unit");
    std::unordered_map<Node, Node, NodeHashFunction> res;
    PreprocessingPassResult pres = bgauss.applyInternal(&apipe);
    TS_ASSERT (pres == PreprocessingPassResult::NO_CONFLICT);
    TS_ASSERT(apipe.size() == 4);

    Node resx1 = d_nm->mkNode(
        kind::EQUAL,
        d_x,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_seven32,
                         d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_two32)),
            d_p));
    Node resy1 = d_nm->mkNode(
        kind::EQUAL,
        d_y,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_nine32,
                         d_nm->mkNode(kind::BITVECTOR_MULT, d_z, d_eight32)),
            d_p));

    Node resx2 = d_nm->mkNode(
        kind::EQUAL,
        d_x,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_two32,
                         d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_three32)),
            d_p));
    Node resz2 = d_nm->mkNode(
        kind::EQUAL,
        d_z,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_three32,
                         d_nm->mkNode(kind::BITVECTOR_MULT, d_y, d_seven32)),
            d_p));

    Node resy3 = d_nm->mkNode(
        kind::EQUAL,
        d_y,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_three32,
                         d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_four32)),
            d_p));
    Node resz3 = d_nm->mkNode(
        kind::EQUAL,
        d_z,
        d_nm->mkNode(
            kind::BITVECTOR_UREM,
            d_nm->mkNode(kind::BITVECTOR_PLUS,
                         d_two32,
                         d_nm->mkNode(kind::BITVECTOR_MULT, d_x, d_six32)),
            d_p));

    bool fx1 = std::find(apipe.begin(), apipe.end(), resx1) != apipe.end();
    bool fy1 = std::find(apipe.begin(), apipe.end(), resy1) != apipe.end();
    bool fx2 = std::find(apipe.begin(), apipe.end(), resx2) != apipe.end();
    bool fz2 = std::find(apipe.begin(), apipe.end(), resz2) != apipe.end();
    bool fy3 = std::find(apipe.begin(), apipe.end(), resy3) != apipe.end();
    bool fz3 = std::find(apipe.begin(), apipe.end(), resz3) != apipe.end();

    /* result depends on order of variables in matrix */
    TS_ASSERT((fx1 && fy1) || (fx2 && fz2) || (fy3 && fz3));
  }

  void testGetMinBw1()
  {
    TS_ASSERT(BVGauss::getMinBwExpr(bv::utils::mkConst(32, 11)) == 4);

    TS_ASSERT(BVGauss::getMinBwExpr(d_p) == 4);
    TS_ASSERT(BVGauss::getMinBwExpr(d_x) == 16);

    Node extp = bv::utils::mkExtract(d_p, 4, 0);
    TS_ASSERT(BVGauss::getMinBwExpr(extp) == 4);
    Node extx = bv::utils::mkExtract(d_x, 4, 0);
    TS_ASSERT(BVGauss::getMinBwExpr(extx) == 5);

    Node zextop8 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(8));
    Node zextop16 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(16));
    Node zextop32 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(32));
    Node zextop40 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(40));

    Node zext40p = d_nm->mkNode(zextop8, d_p);
    TS_ASSERT(BVGauss::getMinBwExpr(zext40p) == 4);
    Node zext40x = d_nm->mkNode(zextop8, d_x);
    TS_ASSERT(BVGauss::getMinBwExpr(zext40x) == 16);

    Node zext48p = d_nm->mkNode(zextop16, d_p);
    TS_ASSERT(BVGauss::getMinBwExpr(zext48p) == 4);
    Node zext48x = d_nm->mkNode(zextop16, d_x);
    TS_ASSERT(BVGauss::getMinBwExpr(zext48x) == 16);

    Node p8 = d_nm->mkConst<BitVector>(BitVector(8, 11u));
    Node x8 = d_nm->mkVar("x8", d_nm->mkBitVectorType(8));

    Node zext48p8 = d_nm->mkNode(zextop40, p8);
    TS_ASSERT(BVGauss::getMinBwExpr(zext48p8) == 4);
    Node zext48x8 = d_nm->mkNode(zextop40, x8);
    TS_ASSERT(BVGauss::getMinBwExpr(zext48x8) == 8);

    Node mult1p = d_nm->mkNode(kind::BITVECTOR_MULT, extp, extp);
    TS_ASSERT(BVGauss::getMinBwExpr(mult1p) == 5);
    Node mult1x = d_nm->mkNode(kind::BITVECTOR_MULT, extx, extx);
    TS_ASSERT(BVGauss::getMinBwExpr(mult1x) == 0);

    Node mult2p = d_nm->mkNode(kind::BITVECTOR_MULT, zext40p, zext40p);
    TS_ASSERT(BVGauss::getMinBwExpr(mult2p) == 7);
    Node mult2x = d_nm->mkNode(kind::BITVECTOR_MULT, zext40x, zext40x);
    TS_ASSERT(BVGauss::getMinBwExpr(mult2x) == 32);

    NodeBuilder<> nbmult3p(kind::BITVECTOR_MULT);
    nbmult3p << zext48p << zext48p << zext48p;
    Node mult3p = nbmult3p;
    TS_ASSERT(BVGauss::getMinBwExpr(mult3p) == 11);
    NodeBuilder<> nbmult3x(kind::BITVECTOR_MULT);
    nbmult3x << zext48x << zext48x << zext48x;
    Node mult3x = nbmult3x;
    TS_ASSERT(BVGauss::getMinBwExpr(mult3x) == 48);

    NodeBuilder<> nbmult4p(kind::BITVECTOR_MULT);
    nbmult4p << zext48p  << zext48p8 << zext48p;
    Node mult4p = nbmult4p;
    TS_ASSERT(BVGauss::getMinBwExpr(mult4p) == 11);
    NodeBuilder<> nbmult4x(kind::BITVECTOR_MULT);
    nbmult4x << zext48x  << zext48x8 << zext48x;
    Node mult4x = nbmult4x;
    TS_ASSERT(BVGauss::getMinBwExpr(mult4x) == 40);

    Node concat1p = bv::utils::mkConcat(d_p, zext48p);
    TS_ASSERT(BVGauss::getMinBwExpr(concat1p) == 52);
    Node concat1x = bv::utils::mkConcat(d_x, zext48x);
    TS_ASSERT(BVGauss::getMinBwExpr(concat1x) == 64);

    Node concat2p = bv::utils::mkConcat(bv::utils::mkZero(16), zext48p);
    TS_ASSERT(BVGauss::getMinBwExpr(concat2p) == 4);
    Node concat2x = bv::utils::mkConcat(bv::utils::mkZero(16), zext48x);
    TS_ASSERT(BVGauss::getMinBwExpr(concat2x) == 16);

    Node udiv1p = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, zext48p, zext48p);
    TS_ASSERT(BVGauss::getMinBwExpr(udiv1p) == 1);
    Node udiv1x = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, zext48x, zext48x);
    TS_ASSERT(BVGauss::getMinBwExpr(udiv1x) == 48);

    Node udiv2p = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, zext48p, zext48p8);
    TS_ASSERT(BVGauss::getMinBwExpr(udiv2p) == 1);
    Node udiv2x = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, zext48x, zext48x8);
    TS_ASSERT(BVGauss::getMinBwExpr(udiv2x) == 48);

    Node urem1p = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48p, zext48p);
    TS_ASSERT(BVGauss::getMinBwExpr(urem1p) == 1);
    Node urem1x = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48x, zext48x);
    TS_ASSERT(BVGauss::getMinBwExpr(urem1x) == 1);

    Node urem2p = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48p, zext48p8);
    TS_ASSERT(BVGauss::getMinBwExpr(urem2p) == 1);
    Node urem2x = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48x, zext48x8);
    TS_ASSERT(BVGauss::getMinBwExpr(urem2x) == 16);

    Node urem3p = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48p8, zext48p);
    TS_ASSERT(BVGauss::getMinBwExpr(urem3p) == 1);
    Node urem3x = d_nm->mkNode(kind::BITVECTOR_UREM_TOTAL, zext48x8, zext48x);
    TS_ASSERT(BVGauss::getMinBwExpr(urem3x) == 8);

    Node add1p = d_nm->mkNode(kind::BITVECTOR_PLUS, extp, extp);
    TS_ASSERT(BVGauss::getMinBwExpr(add1p) == 5);
    Node add1x = d_nm->mkNode(kind::BITVECTOR_PLUS, extx, extx);
    TS_ASSERT(BVGauss::getMinBwExpr(add1x) == 0);

    Node add2p = d_nm->mkNode(kind::BITVECTOR_PLUS, zext40p, zext40p);
    TS_ASSERT(BVGauss::getMinBwExpr(add2p) == 5);
    Node add2x = d_nm->mkNode(kind::BITVECTOR_PLUS, zext40x, zext40x);
    TS_ASSERT(BVGauss::getMinBwExpr(add2x) == 17);

    Node add3p = d_nm->mkNode(kind::BITVECTOR_PLUS, zext48p8, zext48p);
    TS_ASSERT(BVGauss::getMinBwExpr(add3p) == 5);
    Node add3x = d_nm->mkNode(kind::BITVECTOR_PLUS, zext48x8, zext48x);
    TS_ASSERT(BVGauss::getMinBwExpr(add3x) == 17);

    NodeBuilder<> nbadd4p(kind::BITVECTOR_PLUS);
    nbadd4p << zext48p << zext48p << zext48p;
    Node add4p = nbadd4p;
    TS_ASSERT(BVGauss::getMinBwExpr(add4p) == 6);
    NodeBuilder<> nbadd4x(kind::BITVECTOR_PLUS);
    nbadd4x << zext48x << zext48x << zext48x;
    Node add4x = nbadd4x;
    TS_ASSERT(BVGauss::getMinBwExpr(add4x) == 18);

    NodeBuilder<> nbadd5p(kind::BITVECTOR_PLUS);
    nbadd5p << zext48p << zext48p8 << zext48p;
    Node add5p = nbadd5p;
    TS_ASSERT(BVGauss::getMinBwExpr(add5p) == 6);
    NodeBuilder<> nbadd5x(kind::BITVECTOR_PLUS);
    nbadd5x << zext48x << zext48x8 << zext48x;
    Node add5x = nbadd5x;
    TS_ASSERT(BVGauss::getMinBwExpr(add5x) == 18);

    NodeBuilder<> nbadd6p(kind::BITVECTOR_PLUS);
    nbadd6p << zext48p << zext48p << zext48p << zext48p;
    Node add6p = nbadd6p;
    TS_ASSERT(BVGauss::getMinBwExpr(add6p) == 6);
    NodeBuilder<> nbadd6x(kind::BITVECTOR_PLUS);
    nbadd6x << zext48x << zext48x << zext48x << zext48x;
    Node add6x = nbadd6x;
    TS_ASSERT(BVGauss::getMinBwExpr(add6x) == 18);

    Node not1p = d_nm->mkNode(kind::BITVECTOR_NOT, zext40p);
    TS_ASSERT(BVGauss::getMinBwExpr(not1p) == 40);
    Node not1x = d_nm->mkNode(kind::BITVECTOR_NOT, zext40x);
    TS_ASSERT(BVGauss::getMinBwExpr(not1x) == 40);
  }

  void testGetMinBw2()
  {
    /* ((_ zero_extend 5)
     *     ((_ extract 7 0) ((_ zero_extend 15) d_p)))  */
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop15 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(15));
    Node zext1 = d_nm->mkNode(zextop15, d_p);
    Node ext = bv::utils::mkExtract(zext1, 7, 0);
    Node zext2 = d_nm->mkNode(zextop5, ext);
    TS_ASSERT(BVGauss::getMinBwExpr(zext2) == 4);
  }

  void testGetMinBw3a()
  {
    /* ((_ zero_extend 5)
     *     (bvudiv ((_ extract 4 0) ((_ zero_extend 5) (bvudiv x z)))
     *             ((_ extract 4 0) z)))  */
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node z = d_nm->mkVar("z", d_nm->mkBitVectorType(16));
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, x, y);
    Node zext1 = d_nm->mkNode(zextop5, udiv1);
    Node ext1 = bv::utils::mkExtract(zext1, 4, 0);
    Node ext2 = bv::utils::mkExtract(z, 4, 0);
    Node udiv2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1, ext2);
    Node zext2 = bv::utils::mkConcat(bv::utils::mkZero(5), udiv2);
    TS_ASSERT(BVGauss::getMinBwExpr(zext2) == 5);
  }

  void testGetMinBw3b()
  {
    /* ((_ zero_extend 5)
     *     (bvudiv ((_ extract 4 0) ((_ zero_extend 5) (bvudiv x z)))
     *             ((_ extract 4 0) z)))  */
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, d_x, d_y);
    Node zext1 = d_nm->mkNode(zextop5, udiv1);
    Node ext1 = bv::utils::mkExtract(zext1, 4, 0);
    Node ext2 = bv::utils::mkExtract(d_z, 4, 0);
    Node udiv2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1, ext2);
    Node zext2 = bv::utils::mkConcat(bv::utils::mkZero(5), udiv2);
    TS_ASSERT(BVGauss::getMinBwExpr(zext2) == 5);
  }

  void testGetMinBw4a()
  {
    /* (bvadd
     *     ((_ zero_extend 5)
     *         (bvudiv ((_ extract 4 0) ((_ zero_extend 5) (bvudiv x y)))
     *                 ((_ extract 4 0) z)))
     *     ((_ zero_extend 7)
     *         (bvudiv ((_ extract 2 0) ((_ zero_extend 5) (bvudiv x y)))
     *                 ((_ extract 2 0) z)))  */
    Node x = d_nm->mkVar("x", d_nm->mkBitVectorType(16));
    Node y = d_nm->mkVar("y", d_nm->mkBitVectorType(16));
    Node z = d_nm->mkVar("z", d_nm->mkBitVectorType(16));
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop7 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(7));

    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, x, y);
    Node zext1 = d_nm->mkNode(zextop5, udiv1);

    Node ext1_1 = bv::utils::mkExtract(zext1, 4, 0);
    Node ext2_1 = bv::utils::mkExtract(z, 4, 0);
    Node udiv2_1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1_1, ext2_1);
    Node zext2_1 = bv::utils::mkConcat(bv::utils::mkZero(5), udiv2_1);

    Node ext1_2 = bv::utils::mkExtract(zext1, 2, 0);
    Node ext2_2 = bv::utils::mkExtract(z, 2, 0);
    Node udiv2_2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1_2, ext2_2);
    Node zext2_2 = d_nm->mkNode(zextop7, udiv2_2);

    Node plus = d_nm->mkNode(kind::BITVECTOR_PLUS, zext2_1, zext2_2);

    TS_ASSERT(BVGauss::getMinBwExpr(plus) == 6);
  }

  void testGetMinBw4b()
  {
    /* (bvadd
     *     ((_ zero_extend 5)
     *         (bvudiv ((_ extract 4 0) ((_ zero_extend 5) (bvudiv x y)))
     *                 ((_ extract 4 0) z)))
     *     ((_ zero_extend 7)
     *         (bvudiv ((_ extract 2 0) ((_ zero_extend 5) (bvudiv x y)))
     *                 ((_ extract 2 0) z)))  */
    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop7 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(7));

    Node udiv1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, d_x, d_y);
    Node zext1 = d_nm->mkNode(zextop5, udiv1);

    Node ext1_1 = bv::utils::mkExtract(zext1, 4, 0);
    Node ext2_1 = bv::utils::mkExtract(d_z, 4, 0);
    Node udiv2_1 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1_1, ext2_1);
    Node zext2_1 = bv::utils::mkConcat(bv::utils::mkZero(5), udiv2_1);

    Node ext1_2 = bv::utils::mkExtract(zext1, 2, 0);
    Node ext2_2 = bv::utils::mkExtract(d_z, 2, 0);
    Node udiv2_2 = d_nm->mkNode(kind::BITVECTOR_UDIV_TOTAL, ext1_2, ext2_2);
    Node zext2_2 = d_nm->mkNode(zextop7, udiv2_2);

    Node plus = d_nm->mkNode(kind::BITVECTOR_PLUS, zext2_1, zext2_2);

    TS_ASSERT(BVGauss::getMinBwExpr(plus) == 6);
  }

  void testGetMinBw5a()
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
    Node x =bv::utils::mkVar(1);
    Node y =bv::utils::mkVar(1);
    Node z =bv::utils::mkVar(1);
    Node u =bv::utils::mkVar(1);
    Node v =bv::utils::mkVar(1);
    Node w =bv::utils::mkVar(1);
    Node s =bv::utils::mkVar(16);

    Node zextop5 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(5));
    Node zextop15 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(15));

    Node zext15x = d_nm->mkNode(zextop15, x);
    Node zext15y = d_nm->mkNode(zextop15, y);
    Node zext15z = d_nm->mkNode(zextop15, z);
    Node zext15u = d_nm->mkNode(zextop15, u);
    Node zext15v = d_nm->mkNode(zextop15, v);
    Node zext15w = d_nm->mkNode(zextop15, w);

    Node ext7x = bv::utils::mkExtract(zext15x, 7, 0);
    Node ext7y = bv::utils::mkExtract(zext15y, 7, 0);
    Node ext7z = bv::utils::mkExtract(zext15z, 7, 0);
    Node ext7u = bv::utils::mkExtract(zext15u, 7, 0);
    Node ext7v = bv::utils::mkExtract(zext15v, 7, 0);
    Node ext7w = bv::utils::mkExtract(zext15w, 7, 0);
    Node ext7s = bv::utils::mkExtract(s, 7, 0);
    Node ext15s = bv::utils::mkExtract(s, 15, 8);

    Node xx = bv::utils::mkConcat(bv::utils::mkZero(5), ext7x);
    Node yy = bv::utils::mkConcat(bv::utils::mkZero(5), ext7y);
    Node zz = bv::utils::mkConcat(bv::utils::mkZero(5), ext7z);
    Node uu = bv::utils::mkConcat(bv::utils::mkZero(5), ext7u);
    Node vv = bv::utils::mkConcat(bv::utils::mkZero(5), ext7v);
    Node ww = bv::utils::mkConcat(bv::utils::mkZero(5), ext7w);
    Node s7 = bv::utils::mkConcat(bv::utils::mkZero(5), ext7s);
    Node s15 = bv::utils::mkConcat(bv::utils::mkZero(5), ext15s);

    Node plus1 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 86), xx),
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 41), yy));
    Node plus2 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus1,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 37), zz));
    Node plus3 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus2,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 170), uu));
    Node plus4 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus3,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 112), uu));
    Node plus5 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus4,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 195), s15));
    Node plus6 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus5,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 124), s7));
    Node plus7 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus6,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(13, 83), ww));

    TS_ASSERT(BVGauss::getMinBwExpr(plus7) == 0);
  }

  void testGetMinBw5b()
  {
    /* (bvadd
     *   (bvadd
     *     (bvadd
     *       (bvadd
     *         (bvadd
     *           (bvadd
     *             (bvadd (bvmul (_ bv86 20)
     *                           ((_ zero_extend 12)
     *                             ((_ extract 7 0) ((_ zero_extend 15) x))))
     *                    (bvmul (_ bv41 20)
     *                           ((_ zero_extend 12)
     *                             ((_ extract 7 0) ((_ zero_extend 15) y)))))
     *             (bvmul (_ bv37 20)
     *                    ((_ zero_extend 12)
     *                      ((_ extract 7 0) ((_ zero_extend 15) z)))))
     *           (bvmul (_ bv170 20)
     *                  ((_ zero_extend 12)
     *                    ((_ extract 7 0) ((_ zero_extend 15) u)))))
     *         (bvmul (_ bv112 20)
     *                ((_ zero_extend 12)
     *                  ((_ extract 7 0) ((_ zero_extend 15) v)))))
     *       (bvmul (_ bv195 20) ((_ zero_extend 12) ((_ extract 15 8) s))))
     *     (bvmul (_ bv124 20) ((_ zero_extend 12) ((_ extract 7 0) s))))
     *   (bvmul (_ bv83 20)
     *          ((_ zero_extend 12) ((_ extract 7 0) ((_ zero_extend 15) w)))))
     */
    Node x =bv::utils::mkVar(1);
    Node y =bv::utils::mkVar(1);
    Node z =bv::utils::mkVar(1);
    Node u =bv::utils::mkVar(1);
    Node v =bv::utils::mkVar(1);
    Node w =bv::utils::mkVar(1);
    Node s =bv::utils::mkVar(16);

    Node zextop15 = d_nm->mkConst<BitVectorZeroExtend>(BitVectorZeroExtend(15));

    Node zext15x = d_nm->mkNode(zextop15, x);
    Node zext15y = d_nm->mkNode(zextop15, y);
    Node zext15z = d_nm->mkNode(zextop15, z);
    Node zext15u = d_nm->mkNode(zextop15, u);
    Node zext15v = d_nm->mkNode(zextop15, v);
    Node zext15w = d_nm->mkNode(zextop15, w);

    Node ext7x = bv::utils::mkExtract(zext15x, 7, 0);
    Node ext7y = bv::utils::mkExtract(zext15y, 7, 0);
    Node ext7z = bv::utils::mkExtract(zext15z, 7, 0);
    Node ext7u = bv::utils::mkExtract(zext15u, 7, 0);
    Node ext7v = bv::utils::mkExtract(zext15v, 7, 0);
    Node ext7w = bv::utils::mkExtract(zext15w, 7, 0);
    Node ext7s = bv::utils::mkExtract(s, 7, 0);
    Node ext15s = bv::utils::mkExtract(s, 15, 8);

    Node xx = bv::utils::mkConcat(bv::utils::mkZero(12), ext7x);
    Node yy = bv::utils::mkConcat(bv::utils::mkZero(12), ext7y);
    Node zz = bv::utils::mkConcat(bv::utils::mkZero(12), ext7z);
    Node uu = bv::utils::mkConcat(bv::utils::mkZero(12), ext7u);
    Node vv = bv::utils::mkConcat(bv::utils::mkZero(12), ext7v);
    Node ww = bv::utils::mkConcat(bv::utils::mkZero(12), ext7w);
    Node s7 = bv::utils::mkConcat(bv::utils::mkZero(12), ext7s);
    Node s15 = bv::utils::mkConcat(bv::utils::mkZero(12), ext15s);

    Node plus1 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 86), xx),
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 41), yy));
    Node plus2 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus1,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 37), zz));
    Node plus3 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus2,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 170), uu));
    Node plus4 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus3,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 112), uu));
    Node plus5 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus4,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 195), s15));
    Node plus6 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus5,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 124), s7));
    Node plus7 = d_nm->mkNode(
        kind::BITVECTOR_PLUS,
        plus6,
        d_nm->mkNode(kind::BITVECTOR_MULT, bv::utils::mkConst(20, 83), ww));

    TS_ASSERT(BVGauss::getMinBwExpr(plus7) == 19);
    TS_ASSERT(BVGauss::getMinBwExpr(Rewriter::rewrite(plus7)) == 17);
  }

};
