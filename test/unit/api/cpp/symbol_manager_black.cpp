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
 * Black box testing of cvc5::parser::SymbolManager.
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

class TestSymbolManagerBlack : public TestParser
{
 protected:
  TestSymbolManagerBlack() {}
  virtual ~TestSymbolManagerBlack() {}

  void parseAndSetLogic(const std::string& logic)
  {
    std::stringstream ss;
    ss << "(set-logic " << logic << ")" << std::endl;
    InputParser parser(&d_solver, d_symman.get());
    parser.setStreamInput(
        modes::InputLanguage::SMT_LIB_2_6, ss, "parser_black");
    Command cmd = parser.nextCommand();
    ASSERT_NE(cmd.isNull(), true);
    std::stringstream out;
    cmd.invoke(&d_solver, d_symman.get(), out);
  }
};

TEST_F(TestSymbolManagerBlack, isLogicSet)
{
  ASSERT_EQ(d_symman->isLogicSet(), false);
  parseAndSetLogic("QF_LIA");
  ASSERT_EQ(d_symman->isLogicSet(), true);
}

TEST_F(TestSymbolManagerBlack, getLogic)
{
  ASSERT_THROW(d_symman->getLogic(), CVC5ApiException);
  parseAndSetLogic("QF_LIA");
  ASSERT_EQ(d_symman->getLogic(), "QF_LIA");
}

}  // namespace test
}  // namespace cvc5::internal
