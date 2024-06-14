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
 * Black box testing of result functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/check.h"
#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackResult : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
    d_uninterpreted = cvc5_mk_uninterpreted_sort(d_tm, "u");
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }
  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5Sort d_bool;
  Cvc5Sort d_real;
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackResult, is_null)
{
  ASSERT_DEATH(cvc5_result_is_null(nullptr), "invalid result");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_FALSE(cvc5_result_is_null(res));
}

TEST_F(TestCApiBlackResult, is_equal_disequal)
{
  cvc5_set_option(d_solver, "incremental", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res1 = cvc5_check_sat(d_solver);
  cvc5_assert_formula(
      d_solver,
      cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data()));
  Cvc5Result res2 = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_equal(res1, res1));
  ASSERT_FALSE(cvc5_result_is_equal(res1, res2));
  ASSERT_FALSE(cvc5_result_is_equal(res1, nullptr));
  ASSERT_FALSE(cvc5_result_is_equal(nullptr, res1));
  ASSERT_FALSE(cvc5_result_is_disequal(res1, res1));
  ASSERT_TRUE(cvc5_result_is_disequal(res1, res2));
  ASSERT_TRUE(cvc5_result_is_disequal(res1, nullptr));
  ASSERT_TRUE(cvc5_result_is_disequal(nullptr, res1));
}

TEST_F(TestCApiBlackResult, is_sat)
{
  ASSERT_DEATH(cvc5_result_is_sat(nullptr), "invalid result");

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_TRUE(cvc5_result_is_sat(res));
  ASSERT_FALSE(cvc5_result_is_unsat(res));
  ASSERT_FALSE(cvc5_result_is_unknown(res));
}

TEST_F(TestCApiBlackResult, is_unsat)
{
  ASSERT_DEATH(cvc5_result_is_unsat(nullptr), "invalid result");

  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver,
      cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_FALSE(cvc5_result_is_sat(res));
  ASSERT_TRUE(cvc5_result_is_unsat(res));
  ASSERT_FALSE(cvc5_result_is_unknown(res));
}

TEST_F(TestCApiBlackResult, is_unknown)
{
  ASSERT_DEATH(cvc5_result_is_unknown(nullptr), "invalid result");

  cvc5_set_logic(d_solver, "QF_NIA");
  cvc5_set_option(d_solver, "incremental", "false");
  cvc5_set_option(d_solver, "solve-real-as-int", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_real, "x");
  std::vector<Cvc5Term> args = {cvc5_mk_real(d_tm, "0.0"), x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data()));
  args = {x, cvc5_mk_real(d_tm, "1.0")};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_FALSE(cvc5_result_is_sat(res));
  ASSERT_FALSE(cvc5_result_is_unsat(res));
  ASSERT_TRUE(cvc5_result_is_unknown(res));
  Cvc5UnknownExplanation ue = cvc5_result_get_unknown_explanation(res);
  ASSERT_EQ(ue, CVC5_UNKNOWN_EXPLANATION_UNKNOWN_REASON);
  ASSERT_EQ(cvc5_unknown_explanation_to_string(ue),
            std::string("UNKNOWN_REASON"));
}

TEST_F(TestCApiBlackResult, hash)
{
  cvc5_set_option(d_solver, "incremental", "true");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res1 = cvc5_check_sat(d_solver);
  cvc5_assert_formula(
      d_solver,
      cvc5_mk_term(d_tm, CVC5_KIND_DISTINCT, args.size(), args.data()));
  Cvc5Result res2 = cvc5_check_sat(d_solver);
  ASSERT_EQ(cvc5_result_hash(res1), cvc5_result_hash(res1));
  ASSERT_NE(cvc5_result_hash(res1), cvc5_result_hash(res2));
  ASSERT_DEATH(cvc5_result_hash(nullptr), "invalid result");
}

TEST_F(TestCApiBlackResult, copy_release)
{
  ASSERT_DEATH(cvc5_result_copy(nullptr), "invalid result");
  ASSERT_DEATH(cvc5_result_release(nullptr), "invalid result");
  Cvc5Term x = cvc5_mk_const(d_tm, d_uninterpreted, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res1 = cvc5_check_sat(d_solver);
  Cvc5Result res2 = cvc5_result_copy(res1);
  ASSERT_EQ(cvc5_result_hash(res1), cvc5_result_hash(res2));
  cvc5_result_release(res1);
  ASSERT_EQ(cvc5_result_hash(res1), cvc5_result_hash(res2));
  cvc5_result_release(res1);
  // we cannot reliably check that querying on the (now freed) result fails
  // unless ASAN is enabled
}

}  // namespace cvc5::internal::test
