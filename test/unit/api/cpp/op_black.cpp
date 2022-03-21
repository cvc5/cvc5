/******************************************************************************
 * Top contributors (to current version):
 *   Makai Mann, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Op class.
 */

#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiBlackOp : public TestApi
{
};

TEST_F(TestApiBlackOp, getKind)
{
  Op x;
  x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
  ASSERT_NO_THROW(x.getKind());
}

TEST_F(TestApiBlackOp, isNull)
{
  Op x;
  ASSERT_TRUE(x.isNull());
  x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
  ASSERT_FALSE(x.isNull());
}

TEST_F(TestApiBlackOp, opFromKind)
{
  ASSERT_NO_THROW(d_solver.mkOp(ADD));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT), CVC5ApiException);
}

TEST_F(TestApiBlackOp, getNumIndices)
{
  Op plus = d_solver.mkOp(ADD);
  Op divisible = d_solver.mkOp(DIVISIBLE, 4);
  Op bitvector_repeat = d_solver.mkOp(BITVECTOR_REPEAT, 5);
  Op bitvector_zero_extend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6);
  Op bitvector_sign_extend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7);
  Op bitvector_rotate_left = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8);
  Op bitvector_rotate_right = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9);
  Op int_to_bitvector = d_solver.mkOp(INT_TO_BITVECTOR, 10);
  Op iand = d_solver.mkOp(IAND, 3);
  Op floatingpoint_to_ubv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 11);
  Op floatingopint_to_sbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13);
  Op floatingpoint_to_fp_ieee_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, 4, 25);
  Op floatingpoint_to_fp_floatingpoint =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_FP, 4, 25);
  Op floatingpoint_to_fp_real =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_REAL, 4, 25);
  Op floatingpoint_to_fp_signed_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_SBV, 4, 25);
  Op floatingpoint_to_fp_unsigned_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, 4, 25);
  Op floatingpoint_to_fp_generic =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 25);
  Op regexp_loop = d_solver.mkOp(REGEXP_LOOP, 2, 3);

  ASSERT_EQ(0, plus.getNumIndices());
  ASSERT_EQ(1, divisible.getNumIndices());
  ASSERT_EQ(1, bitvector_repeat.getNumIndices());
  ASSERT_EQ(1, bitvector_zero_extend.getNumIndices());
  ASSERT_EQ(1, bitvector_sign_extend.getNumIndices());
  ASSERT_EQ(1, bitvector_rotate_left.getNumIndices());
  ASSERT_EQ(1, bitvector_rotate_right.getNumIndices());
  ASSERT_EQ(1, int_to_bitvector.getNumIndices());
  ASSERT_EQ(1, iand.getNumIndices());
  ASSERT_EQ(1, floatingpoint_to_ubv.getNumIndices());
  ASSERT_EQ(1, floatingopint_to_sbv.getNumIndices());
  ASSERT_EQ(2, floatingpoint_to_fp_ieee_bitvector.getNumIndices());
  ASSERT_EQ(2, floatingpoint_to_fp_floatingpoint.getNumIndices());
  ASSERT_EQ(2, floatingpoint_to_fp_real.getNumIndices());
  ASSERT_EQ(2, floatingpoint_to_fp_signed_bitvector.getNumIndices());
  ASSERT_EQ(2, floatingpoint_to_fp_unsigned_bitvector.getNumIndices());
  ASSERT_EQ(2, floatingpoint_to_fp_generic.getNumIndices());
  ASSERT_EQ(2, regexp_loop.getNumIndices());
}

TEST_F(TestApiBlackOp, subscriptOperator)
{
  Op plus = d_solver.mkOp(ADD);
  Op divisible = d_solver.mkOp(DIVISIBLE, 4);
  Op bitvector_repeat = d_solver.mkOp(BITVECTOR_REPEAT, 4);
  Op bitvector_zero_extend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 4);
  Op bitvector_sign_extend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 4);
  Op bitvector_rotate_left = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 4);
  Op bitvector_rotate_right = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 4);
  Op int_to_bitvector = d_solver.mkOp(INT_TO_BITVECTOR, 4);
  Op iand = d_solver.mkOp(IAND, 4);
  Op floatingpoint_to_ubv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 4);
  Op floatingopint_to_sbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 4);
  Op floatingpoint_to_fp_ieee_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, 4, 5);
  Op floatingpoint_to_fp_floatingpoint =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_FP, 4, 5);
  Op floatingpoint_to_fp_real =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_REAL, 4, 5);
  Op floatingpoint_to_fp_signed_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_SBV, 4, 5);
  Op floatingpoint_to_fp_unsigned_bitvector =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, 4, 5);
  Op floatingpoint_to_fp_generic =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 5);
  Op regexp_loop = d_solver.mkOp(REGEXP_LOOP, 4, 5);

  ASSERT_THROW(plus[0], CVC5ApiException);
  ASSERT_EQ(4, divisible[0].getUInt32Value());
  ASSERT_EQ(4, bitvector_repeat[0].getUInt32Value());
  ASSERT_EQ(4, bitvector_zero_extend[0].getUInt32Value());
  ASSERT_EQ(4, bitvector_sign_extend[0].getUInt32Value());
  ASSERT_EQ(4, bitvector_rotate_left[0].getUInt32Value());
  ASSERT_EQ(4, bitvector_rotate_right[0].getUInt32Value());
  ASSERT_EQ(4, int_to_bitvector[0].getUInt32Value());
  ASSERT_EQ(4, iand[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_ubv[0].getUInt32Value());
  ASSERT_EQ(4, floatingopint_to_sbv[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_fp_ieee_bitvector[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_fp_floatingpoint[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_fp_real[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_fp_signed_bitvector[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_fp_unsigned_bitvector[0].getUInt32Value());
  ASSERT_EQ(4, floatingpoint_to_fp_generic[0].getUInt32Value());
  ASSERT_EQ(4, regexp_loop[0].getUInt32Value());
}


TEST_F(TestApiBlackOp, opScopingToString)
{
  Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
  std::string op_repr = bitvector_repeat_ot.toString();
  Solver solver2;
  ASSERT_EQ(bitvector_repeat_ot.toString(), op_repr);
}
}  // namespace test
}  // namespace cvc5
