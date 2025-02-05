/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of solver functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5_parser.h>
}

#include <fstream>
#include <sstream>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackInputParser : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_sm = cvc5_symbol_manager_new(d_tm);
  }
  void TearDown() override
  {
    cvc5_symbol_manager_delete(d_sm);
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }

  Cvc5Command parse_logic_command(Cvc5InputParser* parser, const char* logic)
  {
    cvc5_parser_set_inc_str_input(
        parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
    std::string str = "(set-logic " + std::string(logic) + ")";
    cvc5_parser_append_inc_str_input(parser, str.c_str());
    const char* error_msg;
    return cvc5_parser_next_command(parser, &error_msg);
  }

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5SymbolManager* d_sm;
};

TEST_F(TestCApiBlackInputParser, get_solver)
{
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  ASSERT_EQ(cvc5_parser_get_solver(parser), d_solver);
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, set_file_input)
{
  ASSERT_DEATH(cvc5_parser_new(nullptr, d_sm), "unexpected NULL argument");

  const char* filename = "parse.smt2";
  std::ofstream smt2(filename);
  smt2 << "(set-logic QF_BV)\n";
  smt2 << "(check-sat)\n";
  smt2 << "(exit)\n" << std::flush;
  smt2.close();
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  cvc5_parser_set_file_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parse.smt2");
  ASSERT_DEATH(cvc5_parser_set_file_input(
                   nullptr, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parse.smt2"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_parser_set_file_input(
                   parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, nullptr),
               "unexpected NULL argument");
  std::remove(filename);
  ASSERT_DEATH(cvc5_parser_set_file_input(
                   parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parse.smt2"),
               "Couldn't open file");
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, set_and_append_inc_str_input)
{
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  ASSERT_FALSE(cvc5_parser_done(parser));

  ASSERT_DEATH(cvc5_parser_set_inc_str_input(
                   nullptr, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_parser_set_inc_str_input(
                   parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, nullptr),
               "unexpected NULL argument");

  ASSERT_DEATH(cvc5_parser_append_inc_str_input(nullptr, "(set-logic ALL)"),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_parser_append_inc_str_input(parser, nullptr),
               "unexpected NULL argument");

  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun a () Bool)");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun b () Int)");

  const char* error_msg;
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  ASSERT_FALSE(cvc5_parser_done(parser));
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_EQ(cmd, nullptr);
  ASSERT_TRUE(cvc5_parser_done(parser));

  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, set_and_append_inc_str_input_interleave)
{
  const char* error_msg;
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  ASSERT_FALSE(cvc5_parser_done(parser));
  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)");
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  cvc5_parser_append_inc_str_input(parser, "(declare-fun a () Bool)");
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  cvc5_parser_append_inc_str_input(parser, "(declare-fun b () Int)");
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  ASSERT_FALSE(cvc5_parser_done(parser));
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_EQ(cmd, nullptr);
  ASSERT_TRUE(cvc5_parser_done(parser));

  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, append_inc_str_no_set)
{
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  ASSERT_DEATH(cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)"),
               "parser not initialized");
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, set_str_input)
{
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);

  ASSERT_DEATH(cvc5_parser_set_str_input(nullptr,
                                         CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
                                         "(set-logic ALL)",
                                         "parser_black"),
               "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_parser_set_str_input(
          parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, nullptr, "parser_black"),
      "unexpected NULL argument");
  ASSERT_DEATH(
      cvc5_parser_set_str_input(
          parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "(set-logic ALL)", nullptr),
      "unexpected NULL argument");

  cvc5_parser_set_str_input(parser,
                            CVC5_INPUT_LANGUAGE_SMT_LIB_2_6,
                            "(set-logic ALL)",
                            "parser_black");

  const char* error_msg;
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_EQ(cmd, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, next_command)
{
  const char* error_msg;
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  ASSERT_DEATH(cvc5_parser_next_command(parser, &error_msg), "not initialized");
  cvc5_parser_set_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "", "parser_black");
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_EQ(cmd, nullptr);
  ASSERT_DEATH(cvc5_parser_next_command(nullptr, &error_msg),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_parser_next_command(parser, nullptr),
               "unexpected NULL argument");
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, next_command_no_input)
{
  const char* error_msg;
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_EQ(cmd, nullptr);
  Cvc5Term t = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_EQ(t, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, next_term)
{
  const char* error_msg;
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, nullptr);
  ASSERT_DEATH(cvc5_parser_next_term(parser, &error_msg), "not initialized");
  cvc5_parser_set_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "", "parser_black");
  Cvc5Term term = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_EQ(term, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_DEATH(cvc5_parser_next_term(nullptr, &error_msg),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_parser_next_term(parser, nullptr),
               "unexpected NULL argument");
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, next_term2)
{
  const char* error_msg;
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, d_sm);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  // parse a declaration command
  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)\n");
  Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  cvc5_parser_append_inc_str_input(parser, "(declare-fun a () Int)\n");
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_NE(cmd, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  // now parse some terms
  cvc5_parser_append_inc_str_input(parser, "45\n");
  Cvc5Term term = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_NE(term, nullptr);
  cvc5_parser_append_inc_str_input(parser, "(+ a 1)\n");
  term = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_NE(term, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  ASSERT_EQ(cvc5_term_get_kind(term), CVC5_KIND_ADD);
  cvc5_parser_append_inc_str_input(parser, "(+ b 1)\n");
  term = cvc5_parser_next_term(parser, &error_msg);
  ASSERT_EQ(term, nullptr);
  ASSERT_NE(error_msg, nullptr);
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, multiple_parsers)
{
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, d_sm);
  // set a logic for the parser
  Cvc5Command cmd = parse_logic_command(parser, "QF_LIA");
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  ASSERT_EQ(cvc5_is_logic_set(d_solver), true);
  ASSERT_EQ(cvc5_get_logic(d_solver), std::string("QF_LIA"));
  ASSERT_EQ(cvc5_sm_is_logic_set(d_sm), true);
  ASSERT_EQ(cvc5_sm_get_logic(d_sm), std::string("QF_LIA"));
  // cannot set logic on solver now
  ASSERT_DEATH(cvc5_set_logic(d_solver, "QF_LRA"), "logic is already set");
  // possible to construct another parser with the same solver and symbol
  // manager
  Cvc5InputParser* parser2 = cvc5_parser_new(d_solver, d_sm);
  // possible to construct another parser with a fresh solver
  Cvc5* solver2 = cvc5_new(d_tm);
  Cvc5InputParser* parser3 = cvc5_parser_new(solver2, d_sm);
  cvc5_parser_set_inc_str_input(
      parser3, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  // logic is automatically set on the solver
  ASSERT_EQ(cvc5_is_logic_set(solver2), true);
  ASSERT_EQ(cvc5_get_logic(solver2), std::string("QF_LIA"));
  // we cannot set the logic since it has already been set
  const char* error_msg;
  cvc5_parser_append_inc_str_input(parser3, "(set-logic QF_LRA");
  cmd = cvc5_parser_next_command(parser, &error_msg);
  ASSERT_EQ(cmd, nullptr);
  ASSERT_EQ(error_msg, nullptr);
  // using a solver with the same logic is allowed
  Cvc5* solver3 = cvc5_new(d_tm);
  cvc5_set_logic(solver3, "QF_LIA");
  Cvc5InputParser* parser4 = cvc5_parser_new(solver3, d_sm);
  cvc5_parser_set_inc_str_input(
      parser4, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  // using a solver with a different logic is not allowed
  Cvc5* solver4 = cvc5_new(d_tm);
  cvc5_set_logic(solver4, "QF_LRA");
  Cvc5InputParser* parser5 = cvc5_parser_new(solver4, d_sm);
  ASSERT_DEATH(cvc5_parser_set_inc_str_input(
                   parser5, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black"),
               "Logic mismatch");
  cvc5_parser_delete(parser5);
  cvc5_parser_delete(parser4);
  cvc5_parser_delete(parser3);
  cvc5_parser_delete(parser2);
  cvc5_parser_delete(parser);
  cvc5_delete(solver4);
  cvc5_delete(solver3);
  cvc5_delete(solver2);
}

TEST_F(TestCApiBlackInputParser, inc_set_Str)
{
  std::vector<const char*> strs{"(set-logic ALL)",
                                "(push)",
                                "(declare-fun x () Int)",
                                "(pop)",
                                "(declare-fun x () Int)"};
  Cvc5Command cmd;
  std::stringstream out;

  Cvc5InputParser* parser = cvc5_parser_new(d_solver, d_sm);

  for (size_t i = 0; i < strs.size(); i++)
  {
    cvc5_parser_set_str_input(
        parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, strs[i], "parser_black");
    const char* error_msg;
    cmd = cvc5_parser_next_command(parser, &error_msg);
    ASSERT_NE(cmd, nullptr);
    out << cvc5_cmd_invoke(cmd, d_solver, d_sm);
  }
  ASSERT_EQ(out.str().empty(), true);
  cvc5_parser_delete(parser);
}

TEST_F(TestCApiBlackInputParser, get_declared_terms_and_sorts)
{
  Cvc5InputParser* parser = cvc5_parser_new(d_solver, d_sm);
  cvc5_parser_set_inc_str_input(
      parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "parser_black");
  cvc5_parser_append_inc_str_input(parser, "(set-logic ALL)");
  cvc5_parser_append_inc_str_input(parser, "(declare-sort U 0)");
  cvc5_parser_append_inc_str_input(parser, "(declare-fun x () U)");

  const char* error_msg;
  for (size_t i = 0; i < 3; i++)
  {
    Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
    ASSERT_NE(cmd, nullptr);
    ASSERT_EQ(error_msg, nullptr);
    (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  }
  size_t size;
  const Cvc5Sort* sorts = cvc5_sm_get_declared_sorts(d_sm, &size);
  ASSERT_EQ(size, 1);
  const Cvc5Term* terms = cvc5_sm_get_declared_terms(d_sm, &size);
  ASSERT_EQ(size, 1);
  ASSERT_TRUE(cvc5_sort_is_equal(cvc5_term_get_sort(terms[0]), sorts[0]));

  cvc5_parser_delete(parser);
}
}  // namespace cvc5::internal::test
