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
 * Blackbox tests involving parametric datatypes of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackParametricDatatype : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_bool = cvc5_get_boolean_sort(d_tm);
  }

  void TearDown() override { cvc5_term_manager_delete(d_tm); }

  Cvc5TermManager* d_tm;
  Cvc5Sort d_bool;
};

TEST_F(TestCApiBlackParametricDatatype, mk_dt_decl_with_params)
{
  Cvc5Sort p = cvc5_mk_param_sort(d_tm, "_x4");
  std::vector<Cvc5Sort> params = {p};
  ASSERT_DEATH(cvc5_mk_dt_decl_with_params(
                   nullptr, "_x0", params.size(), params.data(), false),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_mk_dt_decl_with_params(
                   d_tm, nullptr, params.size(), params.data(), false),
               "unexpected NULL argument");
  (void)cvc5_mk_dt_decl_with_params(d_tm, "_x0", 0, nullptr, false);
}

TEST_F(TestCApiBlackParametricDatatype, proj_issue387)
{
  Cvc5Sort u2 = cvc5_mk_uninterpreted_sort_constructor_sort(d_tm, 1, "_x1");
  Cvc5Sort p1 = cvc5_mk_param_sort(d_tm, "_x4");
  Cvc5Sort p2 = cvc5_mk_param_sort(d_tm, "_x27");

  std::vector<Cvc5Sort> params = {p1};
  (void)cvc5_mk_dt_decl_with_params(
      d_tm, "_x0", params.size(), params.data(), false);
  (void)cvc5_mk_dt_cons_decl(d_tm, "_x18");
  params = {p1, p2};
  ASSERT_DEATH(cvc5_sort_instantiate(u2, params.size(), params.data()),
               "arity mismatch");
}

}  // namespace cvc5::internal::test
