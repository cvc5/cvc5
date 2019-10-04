/*********************                                                        */
/*! \file opterm_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Term class
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class OpTermBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testGetKind();
  void testGetSort();
  void testIsNull();
  void testGetIndicesString();
  void testGetIndicesKind();
  void testGetIndicesUint();
  void testGetIndicesPairUint();

 private:
  Solver d_solver;
};

void OpTermBlack::testGetKind()
{
  OpTerm x;
  TS_ASSERT_THROWS(x.getSort(), CVC4ApiException&);
  x = d_solver.mkOpTerm(BITVECTOR_EXTRACT, 31, 1);
  TS_ASSERT_THROWS_NOTHING(x.getKind());
}

void OpTermBlack::testGetSort()
{
  OpTerm x;
  TS_ASSERT_THROWS(x.getSort(), CVC4ApiException&);
  x = d_solver.mkOpTerm(BITVECTOR_EXTRACT, 31, 1);
  TS_ASSERT_THROWS_NOTHING(x.getSort());
}

void OpTermBlack::testIsNull()
{
  OpTerm x;
  TS_ASSERT(x.isNull());
  x = d_solver.mkOpTerm(BITVECTOR_EXTRACT, 31, 1);
  TS_ASSERT(!x.isNull());
}

void OpTermBlack::testGetIndicesString()
{
  OpTerm x;
  TS_ASSERT_THROWS(x.getIndices<std::string>(), CVC4ApiException&);

  OpTerm divisible_ot = d_solver.mkOpTerm(DIVISIBLE, 4);
  std::string divisible_idx = divisible_ot.getIndices<std::string>();
  TS_ASSERT(divisible_idx == "4");

  OpTerm record_update_ot = d_solver.mkOpTerm(RECORD_UPDATE, "test");
  std::string record_update_idx = record_update_ot.getIndices<std::string>();
  TS_ASSERT(record_update_idx == "test");
  TS_ASSERT_THROWS(record_update_ot.getIndices<uint32_t>(), CVC4ApiException&);
}

void OpTermBlack::testGetIndicesKind()
{
  OpTerm chain_ot = d_solver.mkOpTerm(CHAIN, AND);
  Kind chain_idx = chain_ot.getIndices<Kind>();
  TS_ASSERT(chain_idx == AND);
}

void OpTermBlack::testGetIndicesUint()
{
  OpTerm bitvector_repeat_ot = d_solver.mkOpTerm(BITVECTOR_REPEAT, 5);
  uint32_t bitvector_repeat_idx = bitvector_repeat_ot.getIndices<uint32_t>();
  TS_ASSERT(bitvector_repeat_idx == 5);
  TS_ASSERT_THROWS(
      (bitvector_repeat_ot.getIndices<std::pair<uint32_t, uint32_t>>()),
      CVC4ApiException&);

  OpTerm bitvector_zero_extend_ot = d_solver.mkOpTerm(BITVECTOR_ZERO_EXTEND, 6);
  uint32_t bitvector_zero_extend_idx =
      bitvector_zero_extend_ot.getIndices<uint32_t>();
  TS_ASSERT(bitvector_zero_extend_idx == 6);

  OpTerm bitvector_sign_extend_ot = d_solver.mkOpTerm(BITVECTOR_SIGN_EXTEND, 7);
  uint32_t bitvector_sign_extend_idx =
      bitvector_sign_extend_ot.getIndices<uint32_t>();
  TS_ASSERT(bitvector_sign_extend_idx == 7);

  OpTerm bitvector_rotate_left_ot = d_solver.mkOpTerm(BITVECTOR_ROTATE_LEFT, 8);
  uint32_t bitvector_rotate_left_idx =
      bitvector_rotate_left_ot.getIndices<uint32_t>();
  TS_ASSERT(bitvector_rotate_left_idx == 8);

  OpTerm bitvector_rotate_right_ot =
      d_solver.mkOpTerm(BITVECTOR_ROTATE_RIGHT, 9);
  uint32_t bitvector_rotate_right_idx =
      bitvector_rotate_right_ot.getIndices<uint32_t>();
  TS_ASSERT(bitvector_rotate_right_idx == 9);

  OpTerm int_to_bitvector_ot = d_solver.mkOpTerm(INT_TO_BITVECTOR, 10);
  uint32_t int_to_bitvector_idx = int_to_bitvector_ot.getIndices<uint32_t>();
  TS_ASSERT(int_to_bitvector_idx == 10);

  OpTerm floatingpoint_to_ubv_ot = d_solver.mkOpTerm(FLOATINGPOINT_TO_UBV, 11);
  uint32_t floatingpoint_to_ubv_idx =
      floatingpoint_to_ubv_ot.getIndices<uint32_t>();
  TS_ASSERT(floatingpoint_to_ubv_idx == 11);

  OpTerm floatingpoint_to_ubv_total_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_UBV_TOTAL, 12);
  uint32_t floatingpoint_to_ubv_total_idx =
      floatingpoint_to_ubv_total_ot.getIndices<uint32_t>();
  TS_ASSERT(floatingpoint_to_ubv_total_idx == 12);

  OpTerm floatingpoint_to_sbv_ot = d_solver.mkOpTerm(FLOATINGPOINT_TO_SBV, 13);
  uint32_t floatingpoint_to_sbv_idx =
      floatingpoint_to_sbv_ot.getIndices<uint32_t>();
  TS_ASSERT(floatingpoint_to_sbv_idx == 13);

  OpTerm floatingpoint_to_sbv_total_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_SBV_TOTAL, 14);
  uint32_t floatingpoint_to_sbv_total_idx =
      floatingpoint_to_sbv_total_ot.getIndices<uint32_t>();
  TS_ASSERT(floatingpoint_to_sbv_total_idx == 14);

  OpTerm tuple_update_ot = d_solver.mkOpTerm(TUPLE_UPDATE, 5);
  uint32_t tuple_update_idx = tuple_update_ot.getIndices<uint32_t>();
  TS_ASSERT(tuple_update_idx == 5);
  TS_ASSERT_THROWS(tuple_update_ot.getIndices<std::string>(),
                   CVC4ApiException&);
}

void OpTermBlack::testGetIndicesPairUint()
{
  OpTerm bitvector_extract_ot = d_solver.mkOpTerm(BITVECTOR_EXTRACT, 4, 0);
  std::pair<uint32_t, uint32_t> bitvector_extract_indices =
      bitvector_extract_ot.getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((bitvector_extract_indices == std::pair<uint32_t, uint32_t>{4, 0}));

  OpTerm floatingpoint_to_fp_ieee_bitvector_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_FP_IEEE_BITVECTOR, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_ieee_bitvector_indices =
      floatingpoint_to_fp_ieee_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((floatingpoint_to_fp_ieee_bitvector_indices
             == std::pair<uint32_t, uint32_t>{4, 25}));

  OpTerm floatingpoint_to_fp_floatingpoint_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_FP_FLOATINGPOINT, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_floatingpoint_indices =
      floatingpoint_to_fp_floatingpoint_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((floatingpoint_to_fp_floatingpoint_indices
             == std::pair<uint32_t, uint32_t>{4, 25}));

  OpTerm floatingpoint_to_fp_real_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_FP_REAL, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_real_indices =
      floatingpoint_to_fp_real_ot.getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((floatingpoint_to_fp_real_indices
             == std::pair<uint32_t, uint32_t>{4, 25}));

  OpTerm floatingpoint_to_fp_signed_bitvector_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_signed_bitvector_indices =
      floatingpoint_to_fp_signed_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((floatingpoint_to_fp_signed_bitvector_indices
             == std::pair<uint32_t, uint32_t>{4, 25}));

  OpTerm floatingpoint_to_fp_unsigned_bitvector_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_unsigned_bitvector_indices =
      floatingpoint_to_fp_unsigned_bitvector_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((floatingpoint_to_fp_unsigned_bitvector_indices
             == std::pair<uint32_t, uint32_t>{4, 25}));

  OpTerm floatingpoint_to_fp_generic_ot =
      d_solver.mkOpTerm(FLOATINGPOINT_TO_FP_GENERIC, 4, 25);
  std::pair<uint32_t, uint32_t> floatingpoint_to_fp_generic_indices =
      floatingpoint_to_fp_generic_ot
          .getIndices<std::pair<uint32_t, uint32_t>>();
  TS_ASSERT((floatingpoint_to_fp_generic_indices
             == std::pair<uint32_t, uint32_t>{4, 25}));
  TS_ASSERT_THROWS(floatingpoint_to_fp_generic_ot.getIndices<std::string>(),
                   CVC4ApiException&);
}
