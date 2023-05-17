/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Op class.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackOp : public TestApi
{
};

TEST_F(TestApiBlackOp, hash)
{
  std::hash<cvc5::Op> h;
  ASSERT_NO_THROW(h(d_solver.mkOp(BITVECTOR_EXTRACT, {31, 1})));
}

TEST_F(TestApiBlackOp, getKind)
{
  Op x;
  x = d_solver.mkOp(BITVECTOR_EXTRACT, {31, 1});
  ASSERT_NO_THROW(x.getKind());
}

TEST_F(TestApiBlackOp, isNull)
{
  Op x;
  ASSERT_TRUE(x.isNull());
  Op y = d_solver.mkOp(BITVECTOR_EXTRACT, {31, 1});
  ASSERT_FALSE(y.isNull());
  ASSERT_NE(x, y);
}

TEST_F(TestApiBlackOp, opFromKind)
{
  ASSERT_NO_THROW(d_solver.mkOp(ADD));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT), CVC5ApiException);
}

TEST_F(TestApiBlackOp, getNumIndices)
{
  // Operators with 0 indices
  Op plus = d_solver.mkOp(ADD);

  ASSERT_EQ(0, plus.getNumIndices());

  // Operators with 1 index
  Op divisible = d_solver.mkOp(DIVISIBLE, {4});
  Op bvRepeat = d_solver.mkOp(BITVECTOR_REPEAT, {5});
  Op bvZeroExtend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, {6});
  Op bvSignExtend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, {7});
  Op bvRotateLeft = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, {8});
  Op bvRotateRight = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, {9});
  Op intToBv = d_solver.mkOp(INT_TO_BITVECTOR, {10});
  Op iand = d_solver.mkOp(IAND, {11});
  Op fpToUbv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, {12});
  Op fpToSbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, {13});

  ASSERT_EQ(1, divisible.getNumIndices());
  ASSERT_EQ(1, bvRepeat.getNumIndices());
  ASSERT_EQ(1, bvZeroExtend.getNumIndices());
  ASSERT_EQ(1, bvSignExtend.getNumIndices());
  ASSERT_EQ(1, bvRotateLeft.getNumIndices());
  ASSERT_EQ(1, bvRotateRight.getNumIndices());
  ASSERT_EQ(1, intToBv.getNumIndices());
  ASSERT_EQ(1, iand.getNumIndices());
  ASSERT_EQ(1, fpToUbv.getNumIndices());
  ASSERT_EQ(1, fpToSbv.getNumIndices());

  // Operators with 2 indices
  Op bvExtract = d_solver.mkOp(BITVECTOR_EXTRACT, {1, 0});
  Op toFpFromIeeeBv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {3, 2});
  Op toFpFromFp = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_FP, {5, 4});
  Op toFpFromReal = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_REAL, {7, 6});
  Op toFpFromSbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_SBV, {9, 8});
  Op toFpFromUbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, {11, 10});
  Op regexpLoop = d_solver.mkOp(REGEXP_LOOP, {15, 14});

  ASSERT_EQ(2, bvExtract.getNumIndices());
  ASSERT_EQ(2, toFpFromIeeeBv.getNumIndices());
  ASSERT_EQ(2, toFpFromFp.getNumIndices());
  ASSERT_EQ(2, toFpFromReal.getNumIndices());
  ASSERT_EQ(2, toFpFromSbv.getNumIndices());
  ASSERT_EQ(2, toFpFromUbv.getNumIndices());
  ASSERT_EQ(2, regexpLoop.getNumIndices());

  // Operators with n indices
  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};
  Op tupleProject = d_solver.mkOp(TUPLE_PROJECT, indices);
  ASSERT_EQ(indices.size(), tupleProject.getNumIndices());

  Op relationProject = d_solver.mkOp(RELATION_PROJECT, indices);
  ASSERT_EQ(indices.size(), relationProject.getNumIndices());

  Op tableProject = d_solver.mkOp(TABLE_PROJECT, indices);
  ASSERT_EQ(indices.size(), tableProject.getNumIndices());
}

TEST_F(TestApiBlackOp, subscriptOperator)
{
  // Operators with 0 indices
  Op plus = d_solver.mkOp(ADD);

  ASSERT_THROW(plus[0], CVC5ApiException);

  // Operators with 1 index
  Op divisible = d_solver.mkOp(DIVISIBLE, {4});
  Op bvRepeat = d_solver.mkOp(BITVECTOR_REPEAT, {5});
  Op bvZeroExtend = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, {6});
  Op bvSignExtend = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, {7});
  Op bvRotateLeft = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, {8});
  Op bvRotateRight = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, {9});
  Op intToBv = d_solver.mkOp(INT_TO_BITVECTOR, {10});
  Op iand = d_solver.mkOp(IAND, {11});
  Op fpToUbv = d_solver.mkOp(FLOATINGPOINT_TO_UBV, {12});
  Op fpToSbv = d_solver.mkOp(FLOATINGPOINT_TO_SBV, {13});
  Op regexpRepeat = d_solver.mkOp(REGEXP_REPEAT, {14});

  ASSERT_EQ(4, divisible[0].getUInt32Value());
  ASSERT_EQ(5, bvRepeat[0].getUInt32Value());
  ASSERT_EQ(6, bvZeroExtend[0].getUInt32Value());
  ASSERT_EQ(7, bvSignExtend[0].getUInt32Value());
  ASSERT_EQ(8, bvRotateLeft[0].getUInt32Value());
  ASSERT_EQ(9, bvRotateRight[0].getUInt32Value());
  ASSERT_EQ(10, intToBv[0].getUInt32Value());
  ASSERT_EQ(11, iand[0].getUInt32Value());
  ASSERT_EQ(12, fpToUbv[0].getUInt32Value());
  ASSERT_EQ(13, fpToSbv[0].getUInt32Value());
  ASSERT_EQ(14, regexpRepeat[0].getUInt32Value());

  // Operators with 2 indices
  Op bvExtract = d_solver.mkOp(BITVECTOR_EXTRACT, {1, 0});
  Op toFpFromIeeeBv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {3, 2});
  Op toFpFromFp = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_FP, {5, 4});
  Op toFpFromReal = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_REAL, {7, 6});
  Op toFpFromSbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_SBV, {9, 8});
  Op toFpFromUbv = d_solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, {11, 10});
  Op regexpLoop = d_solver.mkOp(REGEXP_LOOP, {15, 14});

  ASSERT_EQ(1, bvExtract[0].getUInt32Value());
  ASSERT_EQ(0, bvExtract[1].getUInt32Value());
  ASSERT_EQ(3, toFpFromIeeeBv[0].getUInt32Value());
  ASSERT_EQ(2, toFpFromIeeeBv[1].getUInt32Value());
  ASSERT_EQ(5, toFpFromFp[0].getUInt32Value());
  ASSERT_EQ(4, toFpFromFp[1].getUInt32Value());
  ASSERT_EQ(7, toFpFromReal[0].getUInt32Value());
  ASSERT_EQ(6, toFpFromReal[1].getUInt32Value());
  ASSERT_EQ(9, toFpFromSbv[0].getUInt32Value());
  ASSERT_EQ(8, toFpFromSbv[1].getUInt32Value());
  ASSERT_EQ(11, toFpFromUbv[0].getUInt32Value());
  ASSERT_EQ(10, toFpFromUbv[1].getUInt32Value());
  ASSERT_EQ(15, regexpLoop[0].getUInt32Value());
  ASSERT_EQ(14, regexpLoop[1].getUInt32Value());

  // Operators with n indices
  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};
  Op tupleProject = d_solver.mkOp(TUPLE_PROJECT, indices);
  for (size_t i = 0, size = tupleProject.getNumIndices(); i < size; i++)
  {
    ASSERT_EQ(indices[i], tupleProject[i].getUInt32Value());
  }
}

TEST_F(TestApiBlackOp, opScopingToString)
{
  Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, {5});
  std::string op_repr = bitvector_repeat_ot.toString();
  Solver solver2;
  ASSERT_EQ(bitvector_repeat_ot.toString(), op_repr);
  {
    std::stringstream ss;
    ss << bitvector_repeat_ot;
    ASSERT_EQ(ss.str(), op_repr);
  }
}
}  // namespace test
}  // namespace cvc5::internal
