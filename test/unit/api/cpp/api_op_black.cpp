/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  std::hash<Op> h;
  ASSERT_EQ(h(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 1})),
            h(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 1})));
  ASSERT_NE(h(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 1})),
            h(d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 2})));
  (void)std::hash<Op>{}(Op());
}

TEST_F(TestApiBlackOp, getKind)
{
  Op x = d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 1});
  ASSERT_EQ(x.getKind(), Kind::BITVECTOR_EXTRACT);
}

TEST_F(TestApiBlackOp, isNull)
{
  Op x;
  ASSERT_TRUE(x.isNull());
  Op y = d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 1});
  ASSERT_FALSE(y.isNull());
  ASSERT_NE(x, y);
}

TEST_F(TestApiBlackOp, opFromKind)
{
  ASSERT_NO_THROW(d_tm.mkOp(Kind::ADD));
  ASSERT_THROW(d_tm.mkOp(Kind::BITVECTOR_EXTRACT), CVC5ApiException);
}

TEST_F(TestApiBlackOp, getNumIndices)
{
  // Operators with 0 indices
  Op plus = d_tm.mkOp(Kind::ADD);

  ASSERT_EQ(0, plus.getNumIndices());

  // Operators with 1 index
  Op divisible = d_tm.mkOp(Kind::DIVISIBLE, {4});
  Op bvRepeat = d_tm.mkOp(Kind::BITVECTOR_REPEAT, {5});
  Op bvZeroExtend = d_tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {6});
  Op bvSignExtend = d_tm.mkOp(Kind::BITVECTOR_SIGN_EXTEND, {7});
  Op bvRotateLeft = d_tm.mkOp(Kind::BITVECTOR_ROTATE_LEFT, {8});
  Op bvRotateRight = d_tm.mkOp(Kind::BITVECTOR_ROTATE_RIGHT, {9});
  Op intToBv = d_tm.mkOp(Kind::INT_TO_BITVECTOR, {10});
  Op iand = d_tm.mkOp(Kind::IAND, {11});
  Op fpToUbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_UBV, {12});
  Op fpToSbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_SBV, {13});

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
  Op bvExtract = d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {1, 0});
  Op toFpFromIeeeBv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {3, 2});
  Op toFpFromFp = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_FP, {5, 4});
  Op toFpFromReal = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_REAL, {7, 6});
  Op toFpFromSbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_SBV, {9, 8});
  Op toFpFromUbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_UBV, {11, 10});
  Op regexpLoop = d_tm.mkOp(Kind::REGEXP_LOOP, {15, 14});

  ASSERT_EQ(2, bvExtract.getNumIndices());
  ASSERT_EQ(2, toFpFromIeeeBv.getNumIndices());
  ASSERT_EQ(2, toFpFromFp.getNumIndices());
  ASSERT_EQ(2, toFpFromReal.getNumIndices());
  ASSERT_EQ(2, toFpFromSbv.getNumIndices());
  ASSERT_EQ(2, toFpFromUbv.getNumIndices());
  ASSERT_EQ(2, regexpLoop.getNumIndices());

  // Operators with n indices
  std::vector<uint32_t> indices = {0, 3, 2, 0, 1, 2};
  Op tupleProject = d_tm.mkOp(Kind::TUPLE_PROJECT, indices);
  ASSERT_EQ(indices.size(), tupleProject.getNumIndices());

  Op relationProject = d_tm.mkOp(Kind::RELATION_PROJECT, indices);
  ASSERT_EQ(indices.size(), relationProject.getNumIndices());

  Op tableProject = d_tm.mkOp(Kind::TABLE_PROJECT, indices);
  ASSERT_EQ(indices.size(), tableProject.getNumIndices());
}

TEST_F(TestApiBlackOp, subscriptOperator)
{
  // Operators with 0 indices
  Op plus = d_tm.mkOp(Kind::ADD);

  ASSERT_THROW(plus[0], CVC5ApiException);

  // Operators with 1 index
  Op divisible = d_tm.mkOp(Kind::DIVISIBLE, {4});
  Op bvRepeat = d_tm.mkOp(Kind::BITVECTOR_REPEAT, {5});
  Op bvZeroExtend = d_tm.mkOp(Kind::BITVECTOR_ZERO_EXTEND, {6});
  Op bvSignExtend = d_tm.mkOp(Kind::BITVECTOR_SIGN_EXTEND, {7});
  Op bvRotateLeft = d_tm.mkOp(Kind::BITVECTOR_ROTATE_LEFT, {8});
  Op bvRotateRight = d_tm.mkOp(Kind::BITVECTOR_ROTATE_RIGHT, {9});
  Op intToBv = d_tm.mkOp(Kind::INT_TO_BITVECTOR, {10});
  Op iand = d_tm.mkOp(Kind::IAND, {11});
  Op fpToUbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_UBV, {12});
  Op fpToSbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_SBV, {13});
  Op regexpRepeat = d_tm.mkOp(Kind::REGEXP_REPEAT, {14});

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
  Op bvExtract = d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {1, 0});
  Op toFpFromIeeeBv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV, {3, 2});
  Op toFpFromFp = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_FP, {5, 4});
  Op toFpFromReal = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_REAL, {7, 6});
  Op toFpFromSbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_SBV, {9, 8});
  Op toFpFromUbv = d_tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_UBV, {11, 10});
  Op regexpLoop = d_tm.mkOp(Kind::REGEXP_LOOP, {15, 14});

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
  Op tupleProject = d_tm.mkOp(Kind::TUPLE_PROJECT, indices);
  for (size_t i = 0, size = tupleProject.getNumIndices(); i < size; i++)
  {
    ASSERT_EQ(indices[i], tupleProject[i].getUInt32Value());
  }
}

TEST_F(TestApiBlackOp, opScopingToString)
{
  Op bitvector_repeat_ot = d_tm.mkOp(Kind::BITVECTOR_REPEAT, {5});
  std::string op_repr = bitvector_repeat_ot.toString();
  ASSERT_EQ(bitvector_repeat_ot.toString(), op_repr);
  {
    std::stringstream ss;
    ss << bitvector_repeat_ot;
    ASSERT_EQ(ss.str(), op_repr);
  }
}
}  // namespace test
}  // namespace cvc5::internal
