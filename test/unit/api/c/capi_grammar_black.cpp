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
 * Black box testing of grammar-related functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackGrammar : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_bool = cvc5_get_boolean_sort(d_tm);
    d_int = cvc5_get_integer_sort(d_tm);
    d_real = cvc5_get_real_sort(d_tm);
    d_str = cvc5_get_string_sort(d_tm);
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
  Cvc5Sort d_int;
  Cvc5Sort d_real;
  Cvc5Sort d_str;
  Cvc5Sort d_uninterpreted;
};

TEST_F(TestCApiBlackGrammar, to_string)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  std::vector<Cvc5Term> bvars;
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  ASSERT_EQ(cvc5_grammar_to_string(g), std::string(""));
  cvc5_grammar_add_rule(g, start, cvc5_mk_false(d_tm));
  ASSERT_DEATH(cvc5_grammar_to_string(nullptr), "invalid grammar");
  ASSERT_NE(cvc5_grammar_to_string(g), std::string(""));
}

TEST_F(TestCApiBlackGrammar, add_rule)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  Cvc5Term nts = cvc5_mk_var(d_tm, d_bool, "nts");

  std::vector<Cvc5Term> bvars;
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  cvc5_grammar_add_rule(g, start, cvc5_mk_false(d_tm));

  ASSERT_DEATH(cvc5_grammar_add_rule(nullptr, start, cvc5_mk_false(d_tm)),
               "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_rule(g, nullptr, cvc5_mk_false(d_tm)),
               "invalid term");
  ASSERT_DEATH(cvc5_grammar_add_rule(g, start, nullptr), "invalid term");

  ASSERT_DEATH(cvc5_grammar_add_rule(g, nts, cvc5_mk_false(d_tm)),
               "invalid argument");
  ASSERT_DEATH(cvc5_grammar_add_rule(g, start, cvc5_mk_integer_int64(d_tm, 0)),
               "same sort");

  (void)cvc5_synth_fun_with_grammar(d_solver, "f", 0, nullptr, d_bool, g);
  ASSERT_DEATH(cvc5_grammar_add_rule(g, start, cvc5_mk_false(d_tm)),
               "cannot be modified");
}

TEST_F(TestCApiBlackGrammar, add_rules)
{
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  Cvc5Term nts = cvc5_mk_var(d_tm, d_bool, "nts");

  std::vector<Cvc5Term> bvars;
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  std::vector<Cvc5Term> rules = {cvc5_mk_false(d_tm)};
  cvc5_grammar_add_rules(g, start, rules.size(), rules.data());

  ASSERT_DEATH(
      cvc5_grammar_add_rules(nullptr, start, rules.size(), rules.data()),
      "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_rules(g, nullptr, rules.size(), rules.data()),
               "invalid term");
  ASSERT_DEATH(cvc5_grammar_add_rules(g, start, 0, nullptr),
               "unexpected NULL argument");

  ASSERT_DEATH(cvc5_grammar_add_rules(g, nts, rules.size(), rules.data()),
               "invalid argument");
  rules.push_back(nullptr);
  ASSERT_DEATH(cvc5_grammar_add_rules(g, start, rules.size(), rules.data()),
               "invalid term at index 1");
  rules = {cvc5_mk_false(d_tm)};
  ASSERT_DEATH(cvc5_grammar_add_rules(g, nts, rules.size(), rules.data()),
               "invalid argument");
  rules = {cvc5_mk_integer_int64(d_tm, 0)};
  ASSERT_DEATH(cvc5_grammar_add_rules(g, start, rules.size(), rules.data()),
               "Expected term with sort Bool");

  (void)cvc5_synth_fun_with_grammar(d_solver, "f", 0, nullptr, d_bool, g);

  rules = {cvc5_mk_false(d_tm)};
  ASSERT_DEATH(cvc5_grammar_add_rules(g, start, rules.size(), rules.data()),
               "cannot be modified");
}

TEST_F(TestCApiBlackGrammar, add_any_constant)
{
  cvc5_set_option(d_solver, "sygus", "true");

  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  Cvc5Term nts = cvc5_mk_var(d_tm, d_bool, "nts");

  std::vector<Cvc5Term> bvars;
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());

  cvc5_grammar_add_any_constant(g, start);
  cvc5_grammar_add_any_constant(g, start);

  ASSERT_DEATH(cvc5_grammar_add_any_constant(nullptr, start),
               "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_any_constant(g, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_grammar_add_any_constant(g, nts),
               "expected ntSymbol to be one of the non-terminal symbols");

  (void)cvc5_synth_fun_with_grammar(d_solver, "f", 0, nullptr, d_bool, g);

  ASSERT_DEATH(cvc5_grammar_add_any_constant(g, start), "cannot be modified");
}

TEST_F(TestCApiBlackGrammar, add_any_variable)
{
  cvc5_set_option(d_solver, "sygus", "true");

  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  Cvc5Term nts = cvc5_mk_var(d_tm, d_bool, "nts");

  Cvc5Term x = cvc5_mk_var(d_tm, d_bool, "x");
  std::vector<Cvc5Term> bvars = {x};
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g1 = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  Cvc5Grammar g2 =
      cvc5_mk_grammar(d_solver, 0, nullptr, symbols.size(), symbols.data());

  cvc5_grammar_add_any_variable(g1, start);
  cvc5_grammar_add_any_variable(g1, start);
  cvc5_grammar_add_any_variable(g2, start);

  ASSERT_DEATH(cvc5_grammar_add_any_variable(nullptr, start),
               "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_add_any_variable(g1, nullptr), "invalid term");
  ASSERT_DEATH(cvc5_grammar_add_any_variable(g1, nts),
               "expected ntSymbol to be one of the non-terminal symbols");

  (void)cvc5_synth_fun_with_grammar(d_solver, "f", 0, nullptr, d_bool, g1);

  ASSERT_DEATH(cvc5_grammar_add_any_variable(g1, start), "cannot be modified");
}

TEST_F(TestCApiBlackGrammar, equal_hash)
{
  cvc5_set_option(d_solver, "sygus", "true");

  Cvc5Term x = cvc5_mk_var(d_tm, d_bool, "x");
  Cvc5Term start1 = cvc5_mk_var(d_tm, d_bool, "start");
  Cvc5Term start2 = cvc5_mk_var(d_tm, d_bool, "start");
  std::vector<Cvc5Term> bvars, symbols;
  Cvc5Grammar g1, g2;

  {
    symbols = {start1};
    bvars = {};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    ASSERT_EQ(cvc5_grammar_hash(g1), cvc5_grammar_hash(g1));
    ASSERT_EQ(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }

  {
    symbols = {start1};
    bvars = {};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    bvars = {x};
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    ASSERT_NE(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }

  {
    bvars = {x};
    symbols = {start1};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    symbols = {start2};
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    ASSERT_NE(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }

  {
    bvars = {x};
    symbols = {start1};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    cvc5_grammar_add_any_variable(g2, start1);
    ASSERT_NE(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }

  {
    bvars = {x};
    symbols = {start1};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    std::vector<Cvc5Term> rules = {cvc5_mk_false(d_tm)};
    cvc5_grammar_add_rules(g1, start1, rules.size(), rules.data());
    cvc5_grammar_add_rules(g2, start1, rules.size(), rules.data());
    ASSERT_EQ(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }

  {
    bvars = {x};
    symbols = {start1};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    std::vector<Cvc5Term> rules2 = {cvc5_mk_false(d_tm)};
    cvc5_grammar_add_rules(g2, start1, rules2.size(), rules2.data());
    ASSERT_NE(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }

  {
    bvars = {x};
    symbols = {start1};
    g1 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    g2 = cvc5_mk_grammar(
        d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
    std::vector<Cvc5Term> rules1 = {cvc5_mk_true(d_tm)};
    std::vector<Cvc5Term> rules2 = {cvc5_mk_false(d_tm)};
    cvc5_grammar_add_rules(g1, start1, rules1.size(), rules1.data());
    cvc5_grammar_add_rules(g2, start1, rules2.size(), rules2.data());
    ASSERT_NE(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
    ASSERT_TRUE(cvc5_grammar_is_equal(g1, g1));
    ASSERT_FALSE(cvc5_grammar_is_equal(g1, g2));
    ASSERT_TRUE(cvc5_grammar_is_disequal(g1, g2));
  }
  ASSERT_DEATH(cvc5_grammar_hash(nullptr), "invalid grammar");
}

TEST_F(TestCApiBlackGrammar, copy_release)
{
  ASSERT_DEATH(cvc5_grammar_copy(nullptr), "invalid grammar");
  ASSERT_DEATH(cvc5_grammar_release(nullptr), "invalid grammar");
  cvc5_set_option(d_solver, "sygus", "true");
  Cvc5Term start = cvc5_mk_var(d_tm, d_bool, "start");
  Cvc5Term x = cvc5_mk_var(d_tm, d_bool, "x");
  std::vector<Cvc5Term> bvars = {x};
  std::vector<Cvc5Term> symbols = {start};
  Cvc5Grammar g1 = cvc5_mk_grammar(
      d_solver, bvars.size(), bvars.data(), symbols.size(), symbols.data());
  Cvc5Grammar g2 = cvc5_grammar_copy(g1);
  ASSERT_EQ(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
  cvc5_grammar_release(g1);
  ASSERT_EQ(cvc5_grammar_hash(g1), cvc5_grammar_hash(g2));
  cvc5_grammar_release(g1);
  // we cannot reliably check that querying on the (now freed) grammar fails
  // unless ASAN is enabled
}
}  // namespace cvc5::internal::test
