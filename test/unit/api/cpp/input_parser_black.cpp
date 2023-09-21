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
 * Black box testing of cvc5::parser::InputParser SMT-LIbv2 inputs.
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

class TestInputParserBlack : public TestParser
{
 protected:
  TestInputParserBlack() {}
  virtual ~TestInputParserBlack() {}
};


TEST_F(TestInputParserBlack, getSolver)
{
  InputParser p(&d_solver);
  ASSERT_EQ(p.getSolver(), &d_solver);
}

TEST_F(TestInputParserBlack, getSymbolManager)
{
  InputParser p(&d_solver);
  // a symbol manager is allocated
  ASSERT_NE(p.getSymbolManager(), nullptr);

  InputParser p2(&d_solver, d_symman.get());
  ASSERT_EQ(p.getSymbolManager(), d_symman.get());
}

TEST_F(TestInputParserBlack, setStreamInput)
{
  std::stringstream ss;
  ss << "(set-logic QF_LIA)" << std::endl;
  ss << "(declare-fun a () Bool)" << std::endl;
  ss << "(declare-fun b () Int)" << std::endl;
  p.setStreamInput("LANG_SMTLIB_V2_6", ss, "input_parser_black");
  std::unique_ptr<Command> cmd;
  std::stringstream out;
  while ((cmd = p.nextCommand()) != nullptr)
  {
    ASSERT_NO_THROW(cmd->invoke(&d_solver, d_symman.get(), out));
  }
}

TEST_F(TestInputParserBlack, setAndAppendIncrementalStringInput)
{
  p.setIncrementalStringInput("LANG_SMTLIB_V2_6", "input_parser_black");
  std::unique_ptr<Command> cmd;
  p.appendIncrementalStringInput("(set-logic ALL)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.get(), nullptr);
  ASSERT_NO_THROW(cmd->invoke(&d_solver, d_symman.get(), out));
  p.appendIncrementalStringInput("(declare-fun a () Bool)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.get(), nullptr);
  ASSERT_NO_THROW(cmd->invoke(&d_solver, d_symman.get(), out));
  p.appendIncrementalStringInput("(declare-fun b () Int)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.get(), nullptr);
  ASSERT_NO_THROW(cmd->invoke(&d_solver, d_symman.get(), out));
}

TEST_F(TestInputParserBlack, nextCommand)
{
  ASSERT_THROW(p.nextCommand(), CVC5ApiException);
  std::stringstream ss;
  p.setStreamInput("LANG_SMTLIB_V2_6", ss, "input_parser_black");
  ASSERT_EQ(p.nextCommand(), nullptr);
}

TEST_F(TestInputParserBlack, nextTerm)
{
  ASSERT_THROW(p.nextTerm(), CVC5ApiException);
  std::stringstream ss;
  p.setStreamInput("LANG_SMTLIB_V2_6", ss, "input_parser_black");
  ASSERT_EQ(p.nextTerm().isNull(), true);
}


TEST_F(TestInputParserBlack, nextTerm2)
{
  p.setIncrementalStringInput("LANG_SMTLIB_V2_6", "input_parser_black");
  // parse a declaration command
  p.appendIncrementalStringInput("(declare-fun a () Int)");
  std::unique_ptr<Command>  cmd = p.nextCommand();
  ASSERT_NE(cmd.get(), nullptr);
  ASSERT_NO_THROW(cmd->invoke(&d_solver, d_symman.get(), out));
  // now parse some terms
  Term t;
  p.appendIncrementalStringInput("45");
  ASSERT_NO_THROW(t = p.nextTerm());
  ASSERT_EQ(t.isNull(), false);
  p.appendIncrementalStringInput("(+ a 1)");
  ASSERT_NO_THROW(t = p.nextTerm());
  ASSERT_EQ(t.isNull(), false);
  ASSERT_EQ(t.getKind(), Kind::ADD);
  p.appendIncrementalStringInput("(+ b 1)");
  ASSERT_THROW(t = p.nextTerm(), ParserException);

}

}  // namespace test
}  // namespace cvc5::internal
