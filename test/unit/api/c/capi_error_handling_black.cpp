/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the error handling of the cvc5 C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <string>
#include <vector>

#include "gtest/gtest.h"
#include "test_capi.h"

namespace cvc5::internal::test {

class TestCApiBlackErrorHandling : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_release(d_tm);
    cvc5_term_manager_delete(d_tm);
  }
  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
};

TEST_F(TestCApiBlackErrorHandling, no_error_initially)
{
  cvc5_reset_error();
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_STREQ(cvc5_get_error_message(), "");
}

TEST_F(TestCApiBlackErrorHandling, error_is_captured_not_fatal)
{
  // An invalid call records an error instead of terminating the process.
  Cvc5Sort sort = cvc5_sort_array_get_index_sort(nullptr);
  ASSERT_EQ(sort, nullptr);
  ASSERT_TRUE(cvc5_has_error());
  ASSERT_NE(std::string(cvc5_get_error_message()).find("invalid sort"),
            std::string::npos);
}

TEST_F(TestCApiBlackErrorHandling, error_state_resets_on_next_call)
{
  // Trigger an error.
  (void)cvc5_sort_array_get_index_sort(nullptr);
  ASSERT_TRUE(cvc5_has_error());
  // A subsequent successful call clears the error state.
  Cvc5Sort b = cvc5_get_boolean_sort(d_tm);
  ASSERT_NE(b, nullptr);
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_STREQ(cvc5_get_error_message(), "");
}

TEST_F(TestCApiBlackErrorHandling, reset_error)
{
  (void)cvc5_sort_array_get_index_sort(nullptr);
  ASSERT_TRUE(cvc5_has_error());
  cvc5_reset_error();
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_STREQ(cvc5_get_error_message(), "");
}

TEST_F(TestCApiBlackErrorHandling, query_does_not_clear_error)
{
  (void)cvc5_sort_array_get_index_sort(nullptr);
  // Querying the error state must not reset it.
  ASSERT_TRUE(cvc5_has_error());
  ASSERT_TRUE(cvc5_has_error());
  std::string msg = cvc5_get_error_message();
  ASSERT_FALSE(msg.empty());
  ASSERT_EQ(msg, std::string(cvc5_get_error_message()));
}

TEST_F(TestCApiBlackErrorHandling, recover_and_continue)
{
  // Errors do not corrupt the solver: usage continues normally afterwards.
  (void)cvc5_sort_array_get_index_sort(nullptr);
  ASSERT_TRUE(cvc5_has_error());

  Cvc5Sort int_sort = cvc5_get_integer_sort(d_tm);
  Cvc5Term x = cvc5_mk_const(d_tm, int_sort, "x");
  std::vector<Cvc5Term> args = {x, x};
  cvc5_assert_formula(
      d_solver, cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data()));
  Cvc5Result res = cvc5_check_sat(d_solver);
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_TRUE(cvc5_result_is_sat(res));
}

TEST_F(TestCApiBlackErrorHandling, error_message_reflects_most_recent)
{
  // The first error sets the message.
  (void)cvc5_sort_array_get_index_sort(nullptr);
  ASSERT_TRUE(cvc5_has_error());
  std::string first = cvc5_get_error_message();
  ASSERT_NE(first.find("invalid sort"), std::string::npos);

  // A second failing call overwrites it: the message reflects the most recent
  // error, not the first one.
  (void)cvc5_term_get_kind(nullptr);
  ASSERT_TRUE(cvc5_has_error());
  std::string second = cvc5_get_error_message();
  ASSERT_NE(second.find("invalid term"), std::string::npos);
  ASSERT_NE(first, second);
}

TEST_F(TestCApiBlackErrorHandling, captures_non_recoverable_error)
{
  // Errors are not limited to argument validation: a genuine error raised from
  // deep in the solver (here, an ill-typed term) is captured the same way,
  // without aborting the process.
  Cvc5Sort int_sort = cvc5_get_integer_sort(d_tm);
  Cvc5Term i = cvc5_mk_const(d_tm, int_sort, "i");
  Cvc5Term t = cvc5_mk_true(d_tm);
  std::vector<Cvc5Term> args = {i, t};
  // Equating an Integer and a Boolean is ill-typed.
  (void)cvc5_mk_term(d_tm, CVC5_KIND_EQUAL, args.size(), args.data());
  ASSERT_TRUE(cvc5_has_error());
  ASSERT_STRNE(cvc5_get_error_message(), "");

  // The term manager remains usable after such an error.
  Cvc5Term ok = cvc5_mk_term(d_tm, CVC5_KIND_NOT, 1, &t);
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_NE(ok, nullptr);
}

TEST_F(TestCApiBlackErrorHandling, array_getter_returns_null_on_error)
{
  // Regression test for issue #12989: array getters use a thread-local buffer
  // that still holds the result of a previous successful call. On error, they
  // must return NULL rather than that stale (non-NULL) buffer.
  Cvc5Sort int_sort = cvc5_get_integer_sort(d_tm);
  Cvc5Term x = cvc5_mk_const(d_tm, int_sort, "x");
  Cvc5Term zero = cvc5_mk_integer_int64(d_tm, 0);
  std::vector<Cvc5Term> args = {x, zero};
  Cvc5Term gt = cvc5_mk_term(d_tm, CVC5_KIND_GT, args.size(), args.data());
  Cvc5Term lt = cvc5_mk_term(d_tm, CVC5_KIND_LT, args.size(), args.data());

  Cvc5* s1 = cvc5_new(d_tm);
  cvc5_set_option(s1, "produce-unsat-cores", "true");
  cvc5_assert_formula(s1, gt);
  cvc5_assert_formula(s1, lt);
  ASSERT_TRUE(cvc5_result_is_unsat(cvc5_check_sat(s1)));
  size_t size1 = 0;
  const Cvc5Term* core1 = cvc5_get_unsat_core(s1, &size1);
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_NE(core1, nullptr);
  ASSERT_EQ(size1, 2u);

  // Unsat cores are not enabled on this solver, so getting one fails.
  Cvc5* s2 = cvc5_new(d_tm);
  cvc5_assert_formula(s2, gt);
  ASSERT_TRUE(cvc5_result_is_sat(cvc5_check_sat(s2)));
  size_t size2 = 0;
  const Cvc5Term* core2 = nullptr;
  ASSERT_CVC5_ERROR(core2 = cvc5_get_unsat_core(s2, &size2),
                    "cannot get unsat core");
  ASSERT_EQ(core2, nullptr);

  cvc5_delete(s1);
  cvc5_delete(s2);

  // Same for a getter whose result size is given by an input argument.
  Cvc5DatatypeDecl decl = cvc5_mk_dt_decl(d_tm, "list", false);
  Cvc5DatatypeConstructorDecl cons = cvc5_mk_dt_cons_decl(d_tm, "cons");
  cvc5_dt_cons_decl_add_selector(cons, "head", int_sort);
  cvc5_dt_decl_add_constructor(decl, cons);
  Cvc5DatatypeConstructorDecl nil = cvc5_mk_dt_cons_decl(d_tm, "nil");
  cvc5_dt_decl_add_constructor(decl, nil);
  const Cvc5Sort* sorts1 = cvc5_mk_dt_sorts(d_tm, 1, &decl);
  ASSERT_FALSE(cvc5_has_error());
  ASSERT_NE(sorts1, nullptr);
  const Cvc5Sort* sorts2 = nullptr;
  ASSERT_CVC5_ERROR(sorts2 = cvc5_mk_dt_sorts(d_tm, 1, &decl),
                    "is already resolved");
  ASSERT_EQ(sorts2, nullptr);
}

TEST_F(TestCApiBlackErrorHandling, error_macro)
{
  ASSERT_CVC5_ERROR(cvc5_sort_array_get_index_sort(nullptr), "invalid sort");
}

}  // namespace cvc5::internal::test
