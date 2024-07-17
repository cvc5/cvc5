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
 * Black box testing of synthesis result functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/check.h"
#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackSynthResult : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_bool = cvc5_get_boolean_sort(d_tm);
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }
  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5Sort d_bool;
};

TEST_F(TestCApiBlackSynthResult, is_null)
{
  ASSERT_DEATH(cvc5_synth_result_is_null(nullptr), "invalid synthesis result");
}

TEST_F(TestCApiBlackSynthResult, has_solution)
{
  ASSERT_DEATH(cvc5_synth_result_has_solution(nullptr),
               "invalid synthesis result");

  cvc5_set_option(d_solver, "sygus", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  Cvc5Term tbool = cvc5_mk_true(d_tm);
  cvc5_add_sygus_constraint(d_solver, tbool);

  Cvc5SynthResult res = cvc5_check_synth(d_solver);
  ASSERT_FALSE(cvc5_synth_result_is_null(res));
  ASSERT_TRUE(cvc5_synth_result_has_solution(res));
  ASSERT_FALSE(cvc5_synth_result_has_no_solution(res));
  ASSERT_FALSE(cvc5_synth_result_is_unknown(res));
  ASSERT_EQ(cvc5_synth_result_to_string(res), std::string("(SOLUTION)"));
}

TEST_F(TestCApiBlackSynthResult, has_no_solution)
{
  ASSERT_DEATH(cvc5_synth_result_has_no_solution(nullptr),
               "invalid synthesis result");
}

TEST_F(TestCApiBlackSynthResult, is_unknown)
{
  ASSERT_DEATH(cvc5_synth_result_is_unknown(nullptr),
               "invalid synthesis result");

  cvc5_set_option(d_solver, "sygus", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  Cvc5Term tbool = cvc5_mk_false(d_tm);
  cvc5_add_sygus_constraint(d_solver, tbool);
  Cvc5SynthResult res = cvc5_check_synth(d_solver);
  ASSERT_FALSE(cvc5_synth_result_is_null(res));
  ASSERT_FALSE(cvc5_synth_result_has_solution(res));
  ASSERT_TRUE(cvc5_synth_result_has_no_solution(res));
  ASSERT_FALSE(cvc5_synth_result_is_unknown(res));
}

TEST_F(TestCApiBlackSynthResult, is_equal_disequal)
{
  cvc5_set_option(d_solver, "sygus", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  Cvc5Term tfalse = cvc5_mk_false(d_tm);
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  cvc5_add_sygus_constraint(d_solver, ttrue);
  Cvc5SynthResult res1 = cvc5_check_synth(d_solver);
  cvc5_add_sygus_constraint(d_solver, tfalse);
  Cvc5SynthResult res2 = cvc5_check_synth(d_solver);
  ASSERT_TRUE(cvc5_synth_result_is_equal(res1, res1));
  ASSERT_FALSE(cvc5_synth_result_is_equal(res1, res2));
  ASSERT_FALSE(cvc5_synth_result_is_equal(res1, nullptr));
  ASSERT_FALSE(cvc5_synth_result_is_equal(nullptr, res1));
  ASSERT_FALSE(cvc5_synth_result_is_disequal(res1, res1));
  ASSERT_TRUE(cvc5_synth_result_is_disequal(res1, res2));
  ASSERT_TRUE(cvc5_synth_result_is_disequal(res1, nullptr));
  ASSERT_TRUE(cvc5_synth_result_is_disequal(nullptr, res1));
}

TEST_F(TestCApiBlackSynthResult, hash)
{
  cvc5_set_option(d_solver, "sygus", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  Cvc5Term tfalse = cvc5_mk_false(d_tm);
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  cvc5_add_sygus_constraint(d_solver, ttrue);
  Cvc5SynthResult res1 = cvc5_check_synth(d_solver);
  cvc5_add_sygus_constraint(d_solver, tfalse);
  Cvc5SynthResult res2 = cvc5_check_synth(d_solver);
  ASSERT_EQ(cvc5_synth_result_hash(res1), cvc5_synth_result_hash(res1));
  ASSERT_NE(cvc5_synth_result_hash(res1), cvc5_synth_result_hash(res2));
  ASSERT_DEATH(cvc5_synth_result_hash(nullptr), "invalid synthesis result");
}

TEST_F(TestCApiBlackSynthResult, copy_release)
{
  ASSERT_DEATH(cvc5_synth_result_copy(nullptr), "invalid synthesis result");
  ASSERT_DEATH(cvc5_synth_result_release(nullptr), "invalid synthesis result");
  cvc5_set_option(d_solver, "sygus", "true");
  (void)cvc5_synth_fun(d_solver, "f", 0, nullptr, d_bool);
  Cvc5Term ttrue = cvc5_mk_true(d_tm);
  cvc5_add_sygus_constraint(d_solver, ttrue);
  Cvc5SynthResult res1 = cvc5_check_synth(d_solver);
  Cvc5SynthResult res2 = cvc5_synth_result_copy(res1);
  ASSERT_EQ(cvc5_synth_result_hash(res1), cvc5_synth_result_hash(res2));
  cvc5_synth_result_release(res1);
  ASSERT_EQ(cvc5_synth_result_hash(res1), cvc5_synth_result_hash(res2));
  cvc5_synth_result_release(res1);
  // we cannot reliably check that querying on the (now freed) result fails
  // unless ASAN is enabled
}
}  // namespace cvc5::internal::test
