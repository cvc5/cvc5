/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the lifetime guarantees of the parser C API.
 *
 * A symbol manager keeps its term manager alive. Terms and sorts obtained
 * through the parser must remain usable after the parser, symbol manager,
 * solver and term manager that produced them have been deleted.
 *
 * Mirrors test/unit/api/cpp/api_parser_lifetime_black.cpp.
 */

extern "C" {
#include <cvc5/c/cvc5_parser.h>
}

#include <string>
#include <vector>

#include "gtest/gtest.h"
#include "test_capi.h"

namespace cvc5::internal::test {

class TestCApiBlackParserLifetime : public ::testing::Test
{
};

TEST_F(TestCApiBlackParserLifetime, symbolManagerOutlivesTermManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(tm);
  cvc5_term_manager_delete(tm);
  // tm is deleted here; the symbol manager keeps it alive and must still be
  // usable.
  ASSERT_FALSE(cvc5_sm_is_logic_set(sm));
  size_t size;
  (void)cvc5_sm_get_declared_terms(sm, &size);
  ASSERT_EQ(size, 0);
  (void)cvc5_sm_get_declared_sorts(sm, &size);
  ASSERT_EQ(size, 0);
  ASSERT_FALSE(cvc5_has_error());
  cvc5_symbol_manager_delete(sm);
}

TEST_F(TestCApiBlackParserLifetime, declaredSymbolsOutliveParserAndManagers)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(tm);
  Cvc5InputParser* parser = cvc5_parser_new(slv, sm);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_lifetime");
  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)\n");
  cvc5_parser_append_inc_str_input(parser, "(declare-sort U 0)\n");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun a () Int)\n");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun b () U)\n");
  const char* error_msg;
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  while (cmd)
  {
    (void)cvc5_cmd_invoke(cmd, slv, sm);
    cmd = cvc5_parser_next_command(parser, &error_msg);
  }
  size_t nterms, nsorts;
  const Cvc5Term* cterms = cvc5_sm_get_declared_terms(sm, &nterms);
  std::vector<Cvc5Term> terms(cterms, cterms + nterms);
  const Cvc5Sort* csorts = cvc5_sm_get_declared_sorts(sm, &nsorts);
  std::vector<Cvc5Sort> sorts(csorts, csorts + nsorts);
  ASSERT_EQ(terms.size(), 2);
  ASSERT_EQ(sorts.size(), 1);
  cvc5_parser_delete(parser);
  cvc5_symbol_manager_delete(sm);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // The parser, symbol manager, solver and term manager are all deleted
  // here; the declared terms and sorts must still be usable.
  for (Cvc5Term t : terms)
  {
    Cvc5Sort s = cvc5_term_get_sort(t);
    ASSERT_FALSE(std::string(cvc5_term_to_string(t)).empty());
    cvc5_sort_release(s);
    cvc5_term_release(t);
  }
  for (Cvc5Sort s : sorts)
  {
    ASSERT_EQ(std::string(cvc5_sort_to_string(s)), "U");
    cvc5_sort_release(s);
  }
  ASSERT_FALSE(cvc5_has_error());
}

TEST_F(TestCApiBlackParserLifetime, parsedTermOutlivesParserAndManagers)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  Cvc5SymbolManager* sm = cvc5_symbol_manager_new(tm);
  Cvc5InputParser* parser = cvc5_parser_new(slv, sm);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_lifetime");
  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)\n");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun x () Int)\n");
  const char* error_msg;
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  (void)cvc5_cmd_invoke(cmd, slv, sm);
  cmd = cvc5_parser_next_command(parser, &error_msg);
  (void)cvc5_cmd_invoke(cmd, slv, sm);
  cvc5_parser_append_inc_str_input(parser, "(+ x 1)\n");
  Cvc5Term t = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_NE(t, nullptr);
  cvc5_parser_delete(parser);
  cvc5_symbol_manager_delete(sm);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // The parser, symbol manager, solver and term manager are all deleted
  // here; the parsed term must still be usable.
  ASSERT_EQ(cvc5_term_get_kind(t), CVC5_KIND_ADD);
  Cvc5Sort s = cvc5_term_get_sort(t);
  ASSERT_TRUE(cvc5_sort_is_integer(s));
  ASSERT_EQ(std::string(cvc5_term_to_string(t)), "(+ x 1)");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_sort_release(s);
  cvc5_term_release(t);
}

TEST_F(TestCApiBlackParserLifetime,
       parsedTermOutlivesParserWithInternalSymbolManager)
{
  Cvc5TermManager* tm = cvc5_term_manager_new();
  Cvc5* slv = cvc5_new(tm);
  // This parser allocates and owns its own symbol manager.
  Cvc5InputParser* parser = cvc5_parser_new(slv, nullptr);
  Cvc5SymbolManager* sm = cvc5_parser_get_sm(parser);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_lifetime");
  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)\n");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun x () Int)\n");
  const char* error_msg;
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  (void)cvc5_cmd_invoke(cmd, slv, sm);
  cmd = cvc5_parser_next_command(parser, &error_msg);
  (void)cvc5_cmd_invoke(cmd, slv, sm);
  cvc5_parser_append_inc_str_input(parser, "(* x 2)\n");
  Cvc5Term t = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_NE(t, nullptr);
  cvc5_parser_delete(parser);
  cvc5_delete(slv);
  cvc5_term_manager_delete(tm);
  // The parser (and its internally allocated symbol manager), solver and
  // term manager are all deleted here; the parsed term must still be usable.
  ASSERT_EQ(cvc5_term_get_kind(t), CVC5_KIND_MULT);
  Cvc5Sort s = cvc5_term_get_sort(t);
  ASSERT_TRUE(cvc5_sort_is_integer(s));
  ASSERT_EQ(std::string(cvc5_term_to_string(t)), "(* x 2)");
  ASSERT_FALSE(cvc5_has_error());
  cvc5_sort_release(s);
  cvc5_term_release(t);
}

}  // namespace cvc5::internal::test
