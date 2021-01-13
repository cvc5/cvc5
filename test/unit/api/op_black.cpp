/*********************                                                        */
/*! \file op_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Term class
 **/

#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiOpBlack : public TestApi
{
};

TEST_F(TestApiOpBlack, getKind)
{
  Op x;
  x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
  ASSERT_NO_THROW(x.getKind());
}

TEST_F(TestApiOpBlack, isNull)
{
  Op x;
  ASSERT_TRUE(x.isNull());
  x = d_solver.mkOp(BITVECTOR_EXTRACT, 31, 1);
  ASSERT_FALSE(x.isNull());
}

TEST_F(TestApiOpBlack, opFromKind)
{
  Op plus(&d_solver, PLUS);
  ASSERT_FALSE(plus.isIndexed());
  ASSERT_THROW(plus.getIndices<uint32_t>(), CVC4ApiException);

  ASSERT_NO_THROW(d_solver.mkOp(PLUS));
  ASSERT_EQ(plus, d_solver.mkOp(PLUS));
  ASSERT_THROW(d_solver.mkOp(BITVECTOR_EXTRACT), CVC4ApiException);
}

TEST_F(TestApiOpBlack, getIndicesString)
{
  Op x;
  ASSERT_THROW(x.getIndices<std::string>(), CVC4ApiException);

  Op divisible_ot = d_solver.mkOp(DIVISIBLE, 4);
  ASSERT_TRUE(divisible_ot.isIndexed());
  std::string divisible_idx = divisible_ot.getIndices<std::string>();
  ASSERT_EQ(divisible_idx, "4");

  Op record_update_ot = d_solver.mkOp(RECORD_UPDATE, "test");
  std::string record_update_idx = record_update_ot.getIndices<std::string>();
  ASSERT_EQ(record_update_idx, "test");
  ASSERT_THROW(record_update_ot.getIndices<uint32_t>(), CVC4ApiException);
}

TEST_F(TestApiOpBlack, getIndicesUint)
{
  Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
  ASSERT_TRUE(bitvector_repeat_ot.isIndexed());
  uint32_t bitvector_repeat_idx = bitvector_repeat_ot.getIndices<uint32_t>();
  ASSERT_EQ(bitvector_repeat_idx, 5);
  ASSERT_THROW(
      (bitvector_repeat_ot.getIndices<std::pair<uint32_t, uint32_t>>()),
      CVC4ApiException);

  Op bitvector_zero_extend_ot = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, 6);
  uint32_t bitvector_zero_extend_idx =
      bitvector_zero_extend_ot.getIndices<uint32_t>();
  ASSERT_EQ(bitvector_zero_extend_idx, 6);

  Op bitvector_sign_extend_ot = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, 7);
  uint32_t bitvector_sign_extend_idx =
      bitvector_sign_extend_ot.getIndices<uint32_t>();
  ASSERT_EQ(bitvector_sign_extend_idx, 7);

  Op bitvector_rotate_left_ot = d_solver.mkOp(BITVECTOR_ROTATE_LEFT, 8);
  uint32_t bitvector_rotate_left_idx =
      bitvector_rotate_left_ot.getIndices<uint32_t>();
  ASSERT_EQ(bitvector_rotate_left_idx, 8);

  Op bitvector_rotate_right_ot = d_solver.mkOp(BITVECTOR_ROTATE_RIGHT, 9);
  uint32_t bitvector_rotate_right_idx =
      bitvector_rotate_right_ot.getIndices<uint32_t>();
  ASSERT_EQ(bitvector_rotate_right_idx, 9);

  Op int_to_bitvector_ot = d_solver.mkOp(INT_TO_BITVECTOR, 10);
  uint32_t int_to_bitvector_idx = int_to_bitvector_ot.getIndices<uint32_t>();
  ASSERT_EQ(int_to_bitvector_idx, 10);

  Op floatingpoint_to_ubv_ot = d_solver.mkOp(FLOATINGPOINT_TO_UBV, 11);
  uint32_t floatingpoint_to_ubv_idx =
      floatingpoint_to_ubv_ot.getIndices<uint32_t>();
  ASSERT_EQ(floatingpoint_to_ubv_idx, 11);

  Op floatingpoint_to_sbv_ot = d_solver.mkOp(FLOATINGPOINT_TO_SBV, 13);
  uint32_t floatingpoint_to_sbv_idx =
      floatingpoint_to_sbv_ot.getIndices<uint32_t>();
  ASSERT_EQ(floatingpoint_to_sbv_idx, 13);

  Op tuple_update_ot = d_solver.mkOp(TUPLE_UPDATE, 5);
  uint32_t tuple_update_idx = tuple_update_ot.getIndices<uint32_t>();
  ASSERT_EQ(tuple_update_idx, 5);
  ASSERT_THROW(tuple_update_ot.getIndices<std::string>(), CVC4ApiException);
}

TEST_F(TestApiOpBlack, getIndicesPairUint)
{
  Op bitvector_extract_ot = d_solver.mkOp(BITVECTOR_EXTRACT, 4, 0);
  ASSERT_TRUE(bitvector_extract_ot.isIndexed());
  std::pair<uint32_t, uint32_t> bitvector_extract_indices =
      bitvector_extract_ot.getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE(
      (bitvector_extract_indices == std::pair<uint32_t, uint32_t>{4, 0}));

  Op floatingpoint_to_fp_ieee_bitvector_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_ieee_bitvector_indices =
      floatingpoint_to_fp_ieee_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE((floatingpoint_to_fp_ieee_bitvector_indices
               == std::pair<uint32_t, uint32_t>{4, 25}));

  Op floatingpoint_to_fp_floatingpoint_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_FLOATINGPOINT, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_floatingpoint_indices =
      floatingpoint_to_fp_floatingpoint_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE((floatingpoint_to_fp_floatingpoint_indices
               == std::pair<uint32_t, uint32_t>{4, 25}));

  Op floatingpoint_to_fp_real_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_REAL, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_real_indices =
      floatingpoint_to_fp_real_ot.getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE((floatingpoint_to_fp_real_indices
               == std::pair<uint32_t, uint32_t>{4, 25}));

  Op floatingpoint_to_fp_signed_bitvector_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_signed_bitvector_indices =
      floatingpoint_to_fp_signed_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE((floatingpoint_to_fp_signed_bitvector_indices
               == std::pair<uint32_t, uint32_t>{4, 25}));

  Op floatingpoint_to_fp_unsigned_bitvector_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_unsigned_bitvector_indices =
      floatingpoint_to_fp_unsigned_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE((floatingpoint_to_fp_unsigned_bitvector_indices
               == std::pair<uint32_t, uint32_t>{4, 25}));

  Op floatingpoint_to_fp_generic_ot =
      d_solver.mkOp(FLOATINGPOINT_TO_FP_GENERIC, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_generic_indices =
      floatingpoint_to_fp_generic_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  ASSERT_TRUE((floatingpoint_to_fp_generic_indices
               == std::pair<uint32_t, uint32_t>{4, 25}));
  ASSERT_THROW(floatingpoint_to_fp_generic_ot.getIndices<std::string>(),
               CVC4ApiException);
}

TEST_F(TestApiOpBlack, opScopingToString)
{
  Op bitvector_repeat_ot = d_solver.mkOp(BITVECTOR_REPEAT, 5);
  std::string op_repr = bitvector_repeat_ot.toString();
  Solver solver2;
  ASSERT_EQ(bitvector_repeat_ot.toString(), op_repr);
}
}  // namespace test
}  // namespace CVC4
