/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include <cvc5/cvc5_parser.h>
#include "test_parser.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestCommandBlack : public TestParser
{
 protected:
  TestCommandBlack() {}
  virtual ~TestCommandBlack() {}

  Command parseCommand(const std::string& cmdStr)
  {
    std::stringstream ss;
    ss << cmdStr << std::endl;
    InputParser parser(d_solver.get(), d_symman.get());
    parser.setStreamInput(
        modes::InputLanguage::SMT_LIB_2_6, ss, "command_black");
    return parser.nextCommand();
  }
};

TEST_F(TestCommandBlack, invoke)
{
  std::stringstream out;
  Command cmd;
  // set logic command can be executed
  cmd = parseCommand("(set-logic QF_LIA)");
  ASSERT_NE(cmd.isNull(), true);
  cmd.invoke(d_solver.get(), d_symman.get(), out);
  // get model not available
  cmd = parseCommand("(get-model)");
  ASSERT_NE(cmd.isNull(), true);
  cmd.invoke(d_solver.get(), d_symman.get(), out);
  std::string result = out.str();
  ASSERT_EQ(
      "(error \"Cannot get model unless model generation is enabled (try "
      "--produce-models)\")\n",
      result);
  // logic already set
  ASSERT_THROW(parseCommand("(set-logic QF_LRA)"), ParserException);
}

TEST_F(TestCommandBlack, toString)
{
  Command cmd;
  cmd = parseCommand("(set-logic QF_LIA )");
  ASSERT_NE(cmd.isNull(), true);
  // note normalizes wrt whitespace
  ASSERT_EQ(cmd.toString(), "(set-logic QF_LIA)");
  std::stringstream ss;
  ss << cmd;
  ASSERT_EQ(cmd.toString(), ss.str());
}

TEST_F(TestCommandBlack, getCommandName)
{
  Command cmd;
  cmd = parseCommand("(get-model)");
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_EQ(cmd.getCommandName(), "get-model");
}

}  // namespace test
}  // namespace cvc5::internal
