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
 * Black box testing of solver functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5_parser.h>
}

#include <sstream>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackSymbolManager : public ::testing::Test
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
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
    cvc5_symbol_manager_delete(d_sm);
  }

  void parse_and_set_logic(const char* logic)
  {
    const char* error_msg;
    std::stringstream ss;
    ss << "(set-logic " << logic << ")" << std::endl;
    std::string str = ss.str();
    Cvc5InputParser* parser = cvc5_parser_new(d_solver, d_sm);
    cvc5_parser_set_str_input(
        parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, str.c_str(), "parser_black");
    Cvc5Command cmd = cvc5_parser_next_command(parser, &error_msg);
    ASSERT_NE(cmd, nullptr);
    (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  }

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5SymbolManager* d_sm;
};

TEST_F(TestCApiBlackSymbolManager, is_logic_set)
{
  ASSERT_DEATH(cvc5_sm_is_logic_set(nullptr), "unexpected NULL argument");
  ASSERT_EQ(cvc5_sm_is_logic_set(d_sm), false);
  parse_and_set_logic("QF_LIA");
  ASSERT_EQ(cvc5_sm_is_logic_set(d_sm), true);
}

TEST_F(TestCApiBlackSymbolManager, get_logic)
{
  ASSERT_DEATH(cvc5_sm_get_logic(d_sm), "logic has not yet been set");
  parse_and_set_logic("QF_LIA");
  ASSERT_EQ(cvc5_sm_get_logic(d_sm), std::string("QF_LIA"));
  ASSERT_DEATH(cvc5_sm_get_logic(nullptr), "unexpected NULL argument");
}

TEST_F(TestCApiBlackSymbolManager, get_declared_sorts)
{
  size_t size;
  (void)cvc5_sm_get_declared_sorts(d_sm, &size);
  ASSERT_EQ(size, 0);
  ASSERT_DEATH(cvc5_sm_get_declared_sorts(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_sm_get_declared_sorts(d_sm, nullptr), "NULL argument");
}

TEST_F(TestCApiBlackSymbolManager, get_declared_terms)
{
  size_t size;
  (void)cvc5_sm_get_declared_terms(d_sm, &size);
  ASSERT_EQ(size, 0);
  ASSERT_DEATH(cvc5_sm_get_declared_terms(nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_sm_get_declared_terms(d_sm, nullptr), "NULL argument");
}
}  // namespace cvc5::internal::test
