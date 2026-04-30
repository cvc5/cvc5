/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of weight-related functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <string>

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackWeight : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    cvc5_set_option(d_solver, "sygus", "true");
    cvc5_set_logic(d_solver, "NIA");
    d_int = cvc5_get_integer_sort(d_tm);
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5Sort d_int;
};

TEST_F(TestCApiBlackWeight, declare_weight)
{
  Cvc5Weight w = cvc5_declare_weight(d_solver, "w");
  ASSERT_NE(w, nullptr);
  ASSERT_EQ(std::string("w"), cvc5_weight_get_name(w));

  ASSERT_DEATH(cvc5_declare_weight(nullptr, "w"), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_weight(d_solver, nullptr),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_weight_get_name(nullptr), "invalid weight");
}

TEST_F(TestCApiBlackWeight, declare_weight_requires_sygus)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* s = cvc5_new(tm);
  // Without sygus option, declareWeight should fail.
  ASSERT_DEATH(cvc5_declare_weight(s, "w"),
               "cannot call declareWeight unless sygus is enabled");
  cvc5_delete(s);
  cvc5_term_manager_delete(tm);
}

TEST_F(TestCApiBlackWeight, declare_weight_with_default)
{
  Cvc5Term five = cvc5_mk_integer_int64(d_tm, 5);
  Cvc5Weight w = cvc5_declare_weight_with_default(d_solver, "w", five);
  ASSERT_NE(w, nullptr);
  ASSERT_EQ(std::string("w"), cvc5_weight_get_name(w));

  ASSERT_DEATH(cvc5_declare_weight_with_default(nullptr, "w", five),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_weight_with_default(d_solver, nullptr, five),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_declare_weight_with_default(d_solver, "w", nullptr),
               "invalid term");
}

TEST_F(TestCApiBlackWeight, get_default_value)
{
  Cvc5Term five = cvc5_mk_integer_int64(d_tm, 5);
  Cvc5Weight w_default = cvc5_declare_weight_with_default(d_solver, "a", five);
  ASSERT_TRUE(
      cvc5_term_is_equal(cvc5_weight_get_default_value(w_default), five));

  // Weights declared without :default get 0.
  Cvc5Weight w_zero = cvc5_declare_weight(d_solver, "b");
  ASSERT_TRUE(cvc5_term_is_equal(cvc5_weight_get_default_value(w_zero),
                                 cvc5_mk_integer_int64(d_tm, 0)));

  ASSERT_DEATH(cvc5_weight_get_default_value(nullptr), "invalid weight");
}

TEST_F(TestCApiBlackWeight, equal_hash)
{
  Cvc5Weight w1 = cvc5_declare_weight(d_solver, "a");
  Cvc5Weight w2 = cvc5_declare_weight(d_solver, "b");

  ASSERT_TRUE(cvc5_weight_is_equal(w1, w1));
  ASSERT_FALSE(cvc5_weight_is_equal(w1, w2));
  ASSERT_TRUE(cvc5_weight_is_disequal(w1, w2));
  ASSERT_FALSE(cvc5_weight_is_disequal(w1, w1));

  ASSERT_EQ(cvc5_weight_hash(w1), cvc5_weight_hash(w1));

  // NULL handling for equal / disequal.
  ASSERT_TRUE(cvc5_weight_is_equal(nullptr, nullptr));
  ASSERT_FALSE(cvc5_weight_is_equal(w1, nullptr));
  ASSERT_FALSE(cvc5_weight_is_equal(nullptr, w1));
  ASSERT_TRUE(cvc5_weight_is_disequal(w1, nullptr));
  ASSERT_FALSE(cvc5_weight_is_disequal(nullptr, nullptr));

  ASSERT_DEATH(cvc5_weight_hash(nullptr), "invalid weight");
}

TEST_F(TestCApiBlackWeight, mk_weight_symbol)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  Cvc5Term start = cvc5_mk_var(d_tm, d_int, "Start");
  Cvc5Weight w = cvc5_declare_weight(d_solver, "w");

  std::vector<Cvc5Term> bvars = {x};
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  cvc5_grammar_add_rule(g, start, x);

  std::vector<Cvc5Term> fvars = {x};
  Cvc5Term f = cvc5_synth_fun_with_grammar(
      d_solver, "f", fvars.size(), fvars.data(), d_int, g);
  Cvc5Term ws = cvc5_mk_weight_symbol(d_solver, w, f);
  ASSERT_NE(ws, nullptr);
  // The weight symbol has integer sort.
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(ws), d_int));

  ASSERT_DEATH(cvc5_mk_weight_symbol(nullptr, w, f), "unexpected NULL");
  ASSERT_DEATH(cvc5_mk_weight_symbol(d_solver, nullptr, f), "invalid weight");
  ASSERT_DEATH(cvc5_mk_weight_symbol(d_solver, w, nullptr), "invalid term");
}

TEST_F(TestCApiBlackWeight, grammar_add_rule_with_weights)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  Cvc5Term start = cvc5_mk_var(d_tm, d_int, "Start");
  Cvc5Weight w = cvc5_declare_weight(d_solver, "w");

  std::vector<Cvc5Term> bvars = {x};
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  // Add a rule with a weight map.
  std::vector<Cvc5Weight> wkeys = {w};
  std::vector<Cvc5Term> wvals = {cvc5_mk_integer_int64(d_tm, 1)};
  cvc5_grammar_add_rule_with_weights(
      g, start, x, wkeys.size(), wkeys.data(), wvals.data());

  // Add another rule with an empty weight map.
  cvc5_grammar_add_rule_with_weights(
      g, start, cvc5_mk_integer_int64(d_tm, 0), 0, nullptr, nullptr);

  ASSERT_DEATH(cvc5_grammar_add_rule_with_weights(
                   nullptr, start, x, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_rule_with_weights(
                   g, nullptr, x, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid term");
  ASSERT_DEATH(cvc5_grammar_add_rule_with_weights(
                   g, start, nullptr, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid term");
}

TEST_F(TestCApiBlackWeight, grammar_add_rules_with_weights)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  Cvc5Term start = cvc5_mk_var(d_tm, d_int, "Start");
  Cvc5Weight w = cvc5_declare_weight(d_solver, "w");

  std::vector<Cvc5Term> bvars = {x};
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  std::vector<Cvc5Term> rules = {
      cvc5_mk_integer_int64(d_tm, 0), cvc5_mk_integer_int64(d_tm, 1), x};
  // First rule: empty map. Second rule: {w -> 1}. Third rule: {w -> 2}.
  std::vector<size_t> wsizes = {0, 1, 1};
  std::vector<Cvc5Weight> wkeys = {w, w};
  std::vector<Cvc5Term> wvals = {cvc5_mk_integer_int64(d_tm, 1),
                                 cvc5_mk_integer_int64(d_tm, 2)};
  cvc5_grammar_add_rules_with_weights(g,
                                      start,
                                      rules.size(),
                                      rules.data(),
                                      wsizes.data(),
                                      wkeys.data(),
                                      wvals.data());

  // NULL weight_sizes means empty maps for all rules.
  Cvc5Grammar g2 = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  cvc5_grammar_add_rules_with_weights(
      g2, start, rules.size(), rules.data(), nullptr, nullptr, nullptr);
}

TEST_F(TestCApiBlackWeight, grammar_add_any_constant_with_weights)
{
  Cvc5Term start = cvc5_mk_var(d_tm, d_int, "Start");
  Cvc5Weight w = cvc5_declare_weight(d_solver, "w");
  std::vector<Cvc5Term> bvars;
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  std::vector<Cvc5Weight> wkeys = {w};
  std::vector<Cvc5Term> wvals = {cvc5_mk_integer_int64(d_tm, 3)};
  cvc5_grammar_add_any_constant_with_weights(
      g, start, wkeys.size(), wkeys.data(), wvals.data());

  ASSERT_DEATH(cvc5_grammar_add_any_constant_with_weights(
                   nullptr, start, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_any_constant_with_weights(
                   g, nullptr, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid term");
}

TEST_F(TestCApiBlackWeight, grammar_add_any_variable_with_weights)
{
  Cvc5Term x = cvc5_mk_var(d_tm, d_int, "x");
  Cvc5Term start = cvc5_mk_var(d_tm, d_int, "Start");
  Cvc5Weight w = cvc5_declare_weight(d_solver, "w");
  std::vector<Cvc5Term> bvars = {x};
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  std::vector<Cvc5Weight> wkeys = {w};
  std::vector<Cvc5Term> wvals = {cvc5_mk_integer_int64(d_tm, 7)};
  cvc5_grammar_add_any_variable_with_weights(
      g, start, wkeys.size(), wkeys.data(), wvals.data());

  ASSERT_DEATH(cvc5_grammar_add_any_variable_with_weights(
                   nullptr, start, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_any_variable_with_weights(
                   g, nullptr, wkeys.size(), wkeys.data(), wvals.data()),
               "invalid term");
}

TEST_F(TestCApiBlackWeight, copy_release)
{
  ASSERT_DEATH(cvc5_weight_copy(nullptr), "invalid weight");
  ASSERT_DEATH(cvc5_weight_release(nullptr), "invalid weight");

  Cvc5Weight w1 = cvc5_declare_weight(d_solver, "w");
  Cvc5Weight w2 = cvc5_weight_copy(w1);
  ASSERT_EQ(cvc5_weight_hash(w1), cvc5_weight_hash(w2));
  cvc5_weight_release(w1);
  ASSERT_EQ(cvc5_weight_hash(w1), cvc5_weight_hash(w2));
  cvc5_weight_release(w1);
  // we cannot reliably check that querying on the (now freed) weight fails
  // unless ASAN is enabled
}

}  // namespace cvc5::internal::test
