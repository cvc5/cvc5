/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed
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

#include <sstream>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackCommand : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    d_sm = cvc5_symbol_manager_new(d_tm);
    d_parser = cvc5_parser_new(d_solver, d_sm);
    cvc5_parser_set_inc_str_input(
        d_parser, CVC5_INPUT_LANGUAGE_SMT_LIB_2_6, "command_black");
  }
  void TearDown() override
  {
    cvc5_parser_delete(d_parser);
    cvc5_symbol_manager_delete(d_sm);
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }

  void parse_command(const char* str,
                     Cvc5Command* cmd,
                     bool expect_death = false,
                     const std::string& err = "")
  {
    const char* error_msg;
    cvc5_parser_append_inc_str_input(d_parser, str);
    *cmd = cvc5_parser_next_command(d_parser, &error_msg);
    ASSERT_TRUE(expect_death == (error_msg != nullptr));
    ASSERT_TRUE(!expect_death
                || (std::string(error_msg).find(err) != std::string::npos));
  }

  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
  Cvc5SymbolManager* d_sm;
  Cvc5InputParser* d_parser;
};

TEST_F(TestCApiBlackCommand, invoke)
{
  Cvc5Command cmd;
  parse_command("(set-logic QF_LIA)", &cmd);
  ASSERT_NE(cmd, nullptr);
  (void)cvc5_cmd_invoke(cmd, d_solver, d_sm);
  // get model not available
  parse_command("(get-model)", &cmd);
  ASSERT_NE(cmd, nullptr);
  const char* out = cvc5_cmd_invoke(cmd, d_solver, d_sm);
  ASSERT_NE(out, nullptr);
  ASSERT_EQ(
      "(error \"cannot get model unless model generation is enabled (try "
      "--produce-models)\")\n",
      std::string(out));
  ASSERT_DEATH(cvc5_cmd_invoke(nullptr, d_solver, d_sm), "invalid command");
  ASSERT_DEATH(cvc5_cmd_invoke(cmd, nullptr, d_sm), "unexpected NULL argument");
  ASSERT_DEATH(cvc5_cmd_invoke(cmd, d_solver, nullptr),
               "unexpected NULL argument");
  // logic already set
  parse_command(
      "(set-logic QF_LRA)", &cmd, true, "Only one set-logic is allowed");
}

TEST_F(TestCApiBlackCommand, to_string)
{
  Cvc5Command cmd;
  parse_command("(set-logic QF_LIA)", &cmd);
  ASSERT_NE(cmd, nullptr);
  // note normalizes wrt whitespace
  ASSERT_EQ(cvc5_cmd_to_string(cmd), std::string("(set-logic QF_LIA)"));
  ASSERT_DEATH(cvc5_cmd_to_string(nullptr), "invalid command");
}

TEST_F(TestCApiBlackCommand, get_name)
{
  Cvc5Command cmd;
  parse_command("(get-model)", &cmd);
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(cvc5_cmd_get_name(cmd), std::string("get-model"));
  ASSERT_DEATH(cvc5_cmd_get_name(nullptr), "invalid command");
}
}  // namespace cvc5::internal::test
