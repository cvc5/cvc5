/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the C API functions.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackOp : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_int = cvc5_get_integer_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
    d_uninterpreted = cvc5_mk_uninterpreted_sort(d_tm, "u");
  }
  void TearDown() override { cvc5_term_manager_delete(d_tm); }

  Cvc5TermManager* d_tm;
  Cvc5Sort d_bool;
  Cvc5Sort d_int;
  Cvc5Sort d_real;
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackOp, equal)
{
  std::vector<uint32_t> idxs = {4, 0};
  Cvc5Op op1 =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  idxs = {4, 1};
  Cvc5Op op2 =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  ASSERT_TRUE(cvc5_op_is_equal(op1, op1));
  ASSERT_TRUE(cvc5_op_is_disequal(op1, op2));
  ASSERT_FALSE(cvc5_op_is_equal(op1, nullptr));
  ASSERT_TRUE(cvc5_op_is_disequal(op1, nullptr));
}

TEST_F(TestCApiBlackOp, hash)
{
  ASSERT_DEATH(cvc5_op_hash(nullptr), "invalid operator");
  std::vector<uint32_t> idxs = {4, 0};
  Cvc5Op op1 =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  idxs = {4, 1};
  Cvc5Op op2 =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  ASSERT_EQ(cvc5_op_hash(op1), cvc5_op_hash(op1));
  ASSERT_NE(cvc5_op_hash(op1), cvc5_op_hash(op2));
}

TEST_F(TestCApiBlackOp, copy_release)
{
  ASSERT_DEATH(cvc5_op_copy(nullptr), "invalid op");
  ASSERT_DEATH(cvc5_op_release(nullptr), "invalid op");
  std::vector<uint32_t> idxs = {4, 0};
  Cvc5Op op =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  Cvc5Op op_copy = cvc5_op_copy(op);
  size_t hash1 = cvc5_op_hash(op);
  size_t hash2 = cvc5_op_hash(op_copy);
  ASSERT_EQ(hash1, hash2);
  cvc5_op_release(op);
  ASSERT_EQ(cvc5_op_hash(op), cvc5_op_hash(op_copy));
  cvc5_op_release(op);
  // we cannot reliably check that querying on the (now freed) term fails
  // unless ASAN is enabled
}

TEST_F(TestCApiBlackOp, get_kind)
{
  ASSERT_DEATH(cvc5_op_get_kind(nullptr), "invalid operator");
  std::vector<uint32_t> idxs = {4, 0};
  ASSERT_EQ(cvc5_op_get_kind(cvc5_mk_op(
                d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data())),
            CVC5_KIND_BITVECTOR_EXTRACT);
}

TEST_F(TestCApiBlackOp, mk_op)
{
  std::vector<uint32_t> idxs = {4, 0};
  ASSERT_DEATH(
      cvc5_mk_op(
          nullptr, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data()),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), nullptr),
      "unexpected NULL argument");
  (void)cvc5_mk_op(d_tm, CVC5_KIND_ADD, 0, nullptr);
  idxs.push_back(2);
  ASSERT_DEATH(
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data()),
      "invalid number of indices");
}

TEST_F(TestCApiBlackOp, get_num_indices)
{
  ASSERT_DEATH(cvc5_op_get_num_indices(nullptr), "invalid operator");

  // Operators with 0 indices
  Cvc5Op add = cvc5_mk_op(d_tm, CVC5_KIND_ADD, 0, nullptr);
  ASSERT_EQ(cvc5_op_get_num_indices(add), 0);

  // Operators with 1 index
  std::vector<uint32_t> idxs = {4};
  Cvc5Op divisible =
      cvc5_mk_op(d_tm, CVC5_KIND_DIVISIBLE, idxs.size(), idxs.data());
  idxs = {5};
  Cvc5Op bv_repeat =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_REPEAT, idxs.size(), idxs.data());
  idxs = {6};
  Cvc5Op bv_zext = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_ZERO_EXTEND, idxs.size(), idxs.data());
  idxs = {7};
  Cvc5Op bv_sext = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_SIGN_EXTEND, idxs.size(), idxs.data());
  idxs = {8};
  Cvc5Op bv_rol = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_ROTATE_LEFT, idxs.size(), idxs.data());
  idxs = {9};
  Cvc5Op bv_ror = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_ROTATE_RIGHT, idxs.size(), idxs.data());
  idxs = {10};
  Cvc5Op int_to_bv =
      cvc5_mk_op(d_tm, CVC5_KIND_INT_TO_BITVECTOR, idxs.size(), idxs.data());
  idxs = {12};
  Cvc5Op iand = cvc5_mk_op(d_tm, CVC5_KIND_IAND, idxs.size(), idxs.data());
  idxs = {12};
  Cvc5Op fp_to_ubv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_UBV, idxs.size(), idxs.data());
  idxs = {13};
  Cvc5Op fp_to_sbv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_SBV, idxs.size(), idxs.data());

  ASSERT_EQ(1, cvc5_op_get_num_indices(divisible));
  ASSERT_EQ(1, cvc5_op_get_num_indices(bv_repeat));
  ASSERT_EQ(1, cvc5_op_get_num_indices(bv_zext));
  ASSERT_EQ(1, cvc5_op_get_num_indices(bv_sext));
  ASSERT_EQ(1, cvc5_op_get_num_indices(bv_ror));
  ASSERT_EQ(1, cvc5_op_get_num_indices(bv_rol));
  ASSERT_EQ(1, cvc5_op_get_num_indices(int_to_bv));
  ASSERT_EQ(1, cvc5_op_get_num_indices(iand));
  ASSERT_EQ(1, cvc5_op_get_num_indices(fp_to_ubv));
  ASSERT_EQ(1, cvc5_op_get_num_indices(fp_to_sbv));

  // Operators with 2 indices
  idxs = {1, 0};
  Cvc5Op bv_ext =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  idxs = {3, 2};
  Cvc5Op to_fp_from_ieee =
      cvc5_mk_op(d_tm,
                 CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
                 idxs.size(),
                 idxs.data());
  idxs = {5, 4};
  Cvc5Op to_fp_from_fp = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_FP, idxs.size(), idxs.data());
  idxs = {7, 6};
  Cvc5Op to_fp_from_real = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_REAL, idxs.size(), idxs.data());
  idxs = {9, 8};
  Cvc5Op to_fp_from_sbv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_SBV, idxs.size(), idxs.data());
  idxs = {11, 10};
  Cvc5Op to_fp_from_ubv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_UBV, idxs.size(), idxs.data());
  idxs = {15, 14};
  Cvc5Op regexp_loop =
      cvc5_mk_op(d_tm, CVC5_KIND_REGEXP_LOOP, idxs.size(), idxs.data());

  ASSERT_EQ(2, cvc5_op_get_num_indices(bv_ext));
  ASSERT_EQ(2, cvc5_op_get_num_indices(to_fp_from_ieee));
  ASSERT_EQ(2, cvc5_op_get_num_indices(to_fp_from_fp));
  ASSERT_EQ(2, cvc5_op_get_num_indices(to_fp_from_real));
  ASSERT_EQ(2, cvc5_op_get_num_indices(to_fp_from_sbv));
  ASSERT_EQ(2, cvc5_op_get_num_indices(to_fp_from_ubv));
  ASSERT_EQ(2, cvc5_op_get_num_indices(regexp_loop));

  // Operators with n indices
  idxs = {0, 3, 2, 0, 1, 2};
  Cvc5Op tuple_proj =
      cvc5_mk_op(d_tm, CVC5_KIND_TUPLE_PROJECT, idxs.size(), idxs.data());
  ASSERT_EQ(idxs.size(), cvc5_op_get_num_indices(tuple_proj));

  Cvc5Op rel_proj =
      cvc5_mk_op(d_tm, CVC5_KIND_RELATION_PROJECT, idxs.size(), idxs.data());
  ASSERT_EQ(idxs.size(), cvc5_op_get_num_indices(rel_proj));

  Cvc5Op table_proj =
      cvc5_mk_op(d_tm, CVC5_KIND_TABLE_PROJECT, idxs.size(), idxs.data());
  ASSERT_EQ(idxs.size(), cvc5_op_get_num_indices(table_proj));
}

TEST_F(TestCApiBlackOp, subscript_operator)
{
  // Operators with 0 indices
  Cvc5Op add = cvc5_mk_op(d_tm, CVC5_KIND_ADD, 0, nullptr);
  ASSERT_DEATH(cvc5_op_get_index(nullptr, 0), "invalid operator");
  ASSERT_DEATH(cvc5_op_get_index(add, 0), "Op is not indexed");

  // Operators with 1 index
  std::vector<uint32_t> idxs = {4};
  Cvc5Op divisible =
      cvc5_mk_op(d_tm, CVC5_KIND_DIVISIBLE, idxs.size(), idxs.data());
  idxs = {5};
  Cvc5Op bv_repeat =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_REPEAT, idxs.size(), idxs.data());
  idxs = {6};
  Cvc5Op bv_zext = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_ZERO_EXTEND, idxs.size(), idxs.data());
  idxs = {7};
  Cvc5Op bv_sext = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_SIGN_EXTEND, idxs.size(), idxs.data());
  idxs = {8};
  Cvc5Op bv_rol = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_ROTATE_LEFT, idxs.size(), idxs.data());
  idxs = {9};
  Cvc5Op bv_ror = cvc5_mk_op(
      d_tm, CVC5_KIND_BITVECTOR_ROTATE_RIGHT, idxs.size(), idxs.data());
  idxs = {10};
  Cvc5Op int_to_bv =
      cvc5_mk_op(d_tm, CVC5_KIND_INT_TO_BITVECTOR, idxs.size(), idxs.data());
  idxs = {11};
  Cvc5Op iand = cvc5_mk_op(d_tm, CVC5_KIND_IAND, idxs.size(), idxs.data());
  idxs = {12};
  Cvc5Op fp_to_ubv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_UBV, idxs.size(), idxs.data());
  idxs = {13};
  Cvc5Op fp_to_sbv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_SBV, idxs.size(), idxs.data());
  idxs = {14};
  Cvc5Op regexp_repeat =
      cvc5_mk_op(d_tm, CVC5_KIND_REGEXP_REPEAT, idxs.size(), idxs.data());

  ASSERT_EQ(4, cvc5_term_get_uint32_value(cvc5_op_get_index(divisible, 0)));
  ASSERT_EQ(5, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_repeat, 0)));
  ASSERT_EQ(6, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_zext, 0)));
  ASSERT_EQ(7, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_sext, 0)));
  ASSERT_EQ(8, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_rol, 0)));
  ASSERT_EQ(9, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_ror, 0)));
  ASSERT_EQ(10, cvc5_term_get_uint32_value(cvc5_op_get_index(int_to_bv, 0)));
  ASSERT_EQ(11, cvc5_term_get_uint32_value(cvc5_op_get_index(iand, 0)));
  ASSERT_EQ(12, cvc5_term_get_uint32_value(cvc5_op_get_index(fp_to_ubv, 0)));
  ASSERT_EQ(13, cvc5_term_get_uint32_value(cvc5_op_get_index(fp_to_sbv, 0)));
  ASSERT_EQ(14,
            cvc5_term_get_uint32_value(cvc5_op_get_index(regexp_repeat, 0)));

  // Operators with 2 indices
  idxs = {1, 0};
  Cvc5Op bv_ext =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_EXTRACT, idxs.size(), idxs.data());
  idxs = {3, 2};
  Cvc5Op to_fp_from_ieee =
      cvc5_mk_op(d_tm,
                 CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
                 idxs.size(),
                 idxs.data());
  idxs = {5, 4};
  Cvc5Op to_fp_from_fp = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_FP, idxs.size(), idxs.data());
  idxs = {7, 6};
  Cvc5Op to_fp_from_real = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_REAL, idxs.size(), idxs.data());
  idxs = {9, 8};
  Cvc5Op to_fp_from_sbv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_SBV, idxs.size(), idxs.data());
  idxs = {11, 10};
  Cvc5Op to_fp_from_ubv = cvc5_mk_op(
      d_tm, CVC5_KIND_FLOATINGPOINT_TO_FP_FROM_UBV, idxs.size(), idxs.data());
  idxs = {15, 14};
  Cvc5Op regexp_loop =
      cvc5_mk_op(d_tm, CVC5_KIND_REGEXP_LOOP, idxs.size(), idxs.data());

  ASSERT_EQ(1, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_ext, 0)));
  ASSERT_EQ(0, cvc5_term_get_uint32_value(cvc5_op_get_index(bv_ext, 1)));
  ASSERT_EQ(3,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_ieee, 0)));
  ASSERT_EQ(2,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_ieee, 1)));
  ASSERT_EQ(5, cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_fp, 0)));
  ASSERT_EQ(4, cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_fp, 1)));
  ASSERT_EQ(7,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_real, 0)));
  ASSERT_EQ(6,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_real, 1)));
  ASSERT_EQ(9,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_sbv, 0)));
  ASSERT_EQ(8,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_sbv, 1)));
  ASSERT_EQ(11,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_ubv, 0)));
  ASSERT_EQ(10,
            cvc5_term_get_uint32_value(cvc5_op_get_index(to_fp_from_ubv, 1)));
  ASSERT_EQ(15, cvc5_term_get_uint32_value(cvc5_op_get_index(regexp_loop, 0)));
  ASSERT_EQ(14, cvc5_term_get_uint32_value(cvc5_op_get_index(regexp_loop, 1)));

  // Operators with n indices
  idxs = {0, 3, 2, 0, 1, 2};
  Cvc5Op tuple_proj =
      cvc5_mk_op(d_tm, CVC5_KIND_TUPLE_PROJECT, idxs.size(), idxs.data());
  for (size_t i = 0, size = cvc5_op_get_num_indices(tuple_proj); i < size; ++i)
  {
    ASSERT_EQ(idxs[i],
              cvc5_term_get_uint32_value(cvc5_op_get_index(tuple_proj, i)));
  }

  Cvc5Op rel_proj =
      cvc5_mk_op(d_tm, CVC5_KIND_RELATION_PROJECT, idxs.size(), idxs.data());
  for (size_t i = 0, size = cvc5_op_get_num_indices(rel_proj); i < size; ++i)
  {
    ASSERT_EQ(idxs[i],
              cvc5_term_get_uint32_value(cvc5_op_get_index(rel_proj, i)));
  }

  Cvc5Op table_proj =
      cvc5_mk_op(d_tm, CVC5_KIND_TABLE_PROJECT, idxs.size(), idxs.data());
  for (size_t i = 0, size = cvc5_op_get_num_indices(table_proj); i < size; ++i)
  {
    ASSERT_EQ(idxs[i],
              cvc5_term_get_uint32_value(cvc5_op_get_index(table_proj, i)));
  }
}

TEST_F(TestCApiBlackOp, to_string)
{
  std::vector<uint32_t> idxs = {5};
  Cvc5Op bv_repeat =
      cvc5_mk_op(d_tm, CVC5_KIND_BITVECTOR_REPEAT, idxs.size(), idxs.data());
  ASSERT_EQ(cvc5_op_to_string(bv_repeat), cvc5_op_to_string(bv_repeat));
}
}  // namespace cvc5::internal::test
