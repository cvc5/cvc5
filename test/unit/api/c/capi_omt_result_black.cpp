/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of OMT result functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackOmtResult : public ::testing::Test
{};

TEST_F(TestCApiBlackOmtResult, is_null)
{
  ASSERT_DEATH(cvc5_omt_result_is_null(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_optimal)
{
  ASSERT_DEATH(cvc5_omt_result_is_optimal(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_limit_optimal)
{
  ASSERT_DEATH(cvc5_omt_result_is_limit_optimal(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_non_optimal)
{
  ASSERT_DEATH(cvc5_omt_result_is_non_optimal(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_unbounded)  
{
  ASSERT_DEATH(cvc5_omt_result_is_unbounded(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_unsat)
{
  ASSERT_DEATH(cvc5_omt_result_is_unsat(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_unknown)
{  
  ASSERT_DEATH(cvc5_omt_result_is_unknown(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, to_string)
{  
  ASSERT_DEATH(cvc5_omt_result_to_string(nullptr),  "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, is_equal_disequal)
{
  ASSERT_TRUE(cvc5_synth_result_is_equal(nullptr, nullptr));
  ASSERT_FALSE(cvc5_synth_result_is_disequal(nullptr, nullptr));  
}

TEST_F(TestCApiBlackOmtResult, hash)
{
  ASSERT_DEATH(cvc5_omt_result_hash(nullptr), "invalid OMT result");
}

TEST_F(TestCApiBlackOmtResult, copy_release)
{
  ASSERT_DEATH(cvc5_omt_result_copy(nullptr), "invalid OMT result");
  ASSERT_DEATH(cvc5_omt_result_release(nullptr), "invalid OMT result");
}
}  // namespace cvc5::internal::test
