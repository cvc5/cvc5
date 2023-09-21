/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::parser::Command.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <sstream>

#include "base/output.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/parser_exception.h"
#include "test_parser.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestCommandBlack : public TestParser
{
 protected:
  TestCommandBlack() {}
  virtual ~TestCommandBlack() {}

  std::unique_ptr<Command> parseCommand(const std::string& cmdStr)
  {
    std::stringstream ss;
    ss << cmdStr << std::endl;
    InputParser parser(&d_solver, d_symman.get());
    parser.setStreamInput("LANG_SMTLIB_V2_6", ss, "parser_black");
    return parser.nextCommand();
  }
};


TEST_F(TestCommandBlack, invoke)
{
  std::stringstream out;
  std::unique_ptr<Command> cmd;
  // set logic command can be executed
  cmd = parseCommand("(set-logic QF_LIA)");
  ASSERT_NE(cmd, nullptr);
  cmd->invoke(&d_solver, d_symman.get(), out);
  // get model not available
  cmd = parseCommand("(get-model)");
  ASSERT_NE(cmd, nullptr);
  cmd->invoke(&d_solver, d_symman.get(), out);
  // logic already set
  /*
  cmd = parseCommand("(set-logic QF_LRA)");
  ASSERT_NE(cmd, nullptr);
  ASSERT_THROW(cmd->invoke(&d_solver, d_symman.get(), out), CVC5ApiException);
  */
}

TEST_F(TestCommandBlack, toString)
{
  std::unique_ptr<Command> cmd;
  cmd = parseCommand("(set-logic QF_LIA )");
  ASSERT_NE(cmd, nullptr);
  // note normalizes wrt whitespace
  ASSERT_EQ(cmd->toString(), "(set-logic QF_LIA)\n");
}

TEST_F(TestCommandBlack, getCommandName)
{
  std::unique_ptr<Command> cmd;
  cmd = parseCommand("(get-model)");
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(cmd->getCommandName(), "get-model");
}

TEST_F(TestCommandBlack, commandStatus)
{
  std::stringstream out;
  std::unique_ptr<Command> cmd;

  cmd = parseCommand("(set-logic QF_LIA)");
  ASSERT_NE(cmd, nullptr);
  ASSERT_EQ(cmd->ok(), true);
  cmd->invoke(&d_solver, d_symman.get(), out);
  ASSERT_EQ(cmd->ok(), true);
  ASSERT_EQ(cmd->fail(), false);
  ASSERT_EQ(cmd->interrupted(), false);

  cmd = parseCommand("(get-model)");
  ASSERT_NE(cmd, nullptr);
  cmd->invoke(&d_solver, d_symman.get(), out);
  ASSERT_EQ(cmd->ok(), false);
  //ASSERT_EQ(cmd->fail(), true);
  ASSERT_EQ(cmd->interrupted(), false);
}

}  // namespace test
}  // namespace cvc5::internal
