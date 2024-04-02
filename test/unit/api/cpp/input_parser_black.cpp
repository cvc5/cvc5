/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "test_parser.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestInputParserBlack : public TestParser
{
 protected:
  TestInputParserBlack() {}
  virtual ~TestInputParserBlack() {}

  Command parseLogicCommand(InputParser& p, const std::string& logic)
  {
    p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                "input_parser_black");
    std::stringstream ss;
    ss << "(set-logic " << logic << ")" << std::endl;
    p.appendIncrementalStringInput(ss.str());
    return p.nextCommand();
  }
};

TEST_F(TestInputParserBlack, getSolver)
{
  InputParser p(d_solver.get());
  ASSERT_EQ(p.getSolver(), d_solver.get());
}

TEST_F(TestInputParserBlack, getSymbolManager)
{
  InputParser p(d_solver.get());
  // a symbol manager is allocated
  ASSERT_NE(p.getSymbolManager(), nullptr);

  InputParser p2(d_solver.get(), d_symman.get());
  ASSERT_EQ(p2.getSymbolManager(), d_symman.get());
}

TEST_F(TestInputParserBlack, setFileInput)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(
      p.setFileInput(modes::InputLanguage::SMT_LIB_2_6, "nonexistent.smt2"),
      CVC5ApiException);
}

TEST_F(TestInputParserBlack, setStreamInput)
{
  InputParser p(d_solver.get());
  std::stringstream ss;
  ss << "(set-logic QF_LIA)" << std::endl;
  ss << "(declare-fun a () Bool)" << std::endl;
  ss << "(declare-fun b () Int)" << std::endl;
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "input_parser_black");
  ASSERT_EQ(p.done(), false);
  Command cmd;
  std::stringstream out;
  while (true)
  {
    cmd = p.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  }
  ASSERT_EQ(p.done(), true);
}

TEST_F(TestInputParserBlack, setAndAppendIncrementalStringInput)
{
  std::stringstream out;
  InputParser p(d_solver.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  Command cmd;
  p.appendIncrementalStringInput("(set-logic ALL)");
  p.appendIncrementalStringInput("(declare-fun a () Bool)");
  p.appendIncrementalStringInput("(declare-fun b () Int)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
}

TEST_F(TestInputParserBlack, setAndAppendIncrementalStringInputInterleave)
{
  std::stringstream out;
  InputParser p(d_solver.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  Command cmd;
  p.appendIncrementalStringInput("(set-logic ALL)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  p.appendIncrementalStringInput("(declare-fun a () Bool)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  p.appendIncrementalStringInput("(declare-fun b () Int)");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
}

TEST_F(TestInputParserBlack, appendIncrementalNoSet)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(p.appendIncrementalStringInput("(set-logic ALL)"),
               CVC5ApiException);
}

TEST_F(TestInputParserBlack, setStringInput)
{
  std::stringstream out;
  InputParser p(d_solver.get());
  Command cmd;
  p.setStringInput(modes::InputLanguage::SMT_LIB_2_6,
                   "(set-logic ALL)",
                   "input_parser_black");
  cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  cmd = p.nextCommand();
  ASSERT_EQ(cmd.isNull(), true);
}

TEST_F(TestInputParserBlack, nextCommand)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(p.nextCommand(), CVC5ApiException);
  std::stringstream ss;
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "input_parser_black");
  Command cmd = p.nextCommand();
  ASSERT_EQ(cmd.isNull(), true);
}

TEST_F(TestInputParserBlack, nextCommandNoInput)
{
  InputParser p(d_solver.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  Command cmd = p.nextCommand();
  ASSERT_EQ(cmd.isNull(), true);
  Term t = p.nextTerm();
  ASSERT_EQ(t.isNull(), true);
}

TEST_F(TestInputParserBlack, nextTerm)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(p.nextTerm(), CVC5ApiException);
  std::stringstream ss;
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "input_parser_black");
  ASSERT_EQ(p.nextTerm().isNull(), true);
}

TEST_F(TestInputParserBlack, nextTerm2)
{
  std::stringstream out;
  InputParser p(d_solver.get(), d_symman.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  // parse a declaration command
  p.appendIncrementalStringInput("(declare-fun a () Int)\n");
  Command cmd = p.nextCommand();
  ASSERT_NE(cmd.isNull(), true);
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  // now parse some terms
  Term t;
  p.appendIncrementalStringInput("45\n");
  ASSERT_NO_THROW(t = p.nextTerm());
  ASSERT_EQ(t.isNull(), false);
  p.appendIncrementalStringInput("(+ a 1)\n");
  ASSERT_NO_THROW(t = p.nextTerm());
  ASSERT_EQ(t.isNull(), false);
  ASSERT_EQ(t.getKind(), Kind::ADD);
  p.appendIncrementalStringInput("(+ b 1)\n");
  ASSERT_THROW(t = p.nextTerm(), ParserException);
}

TEST_F(TestInputParserBlack, multipleParsers)
{
  std::stringstream out;
  InputParser p(d_solver.get(), d_symman.get());
  // set a logic for the parser
  Command cmd = parseLogicCommand(p, "QF_LIA");
  ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  ASSERT_EQ(d_solver->isLogicSet(), true);
  ASSERT_EQ(d_solver->getLogic(), "QF_LIA");
  ASSERT_EQ(d_symman->isLogicSet(), true);
  ASSERT_EQ(d_symman->getLogic(), "QF_LIA");
  // cannot set logic on solver now
  ASSERT_THROW(d_solver->setLogic("QF_LRA"), CVC5ApiException);

  // possible to construct another parser with the same solver and symbol
  // manager
  InputParser p2(d_solver.get(), p.getSymbolManager());

  // possible to construct another parser with a fresh solver
  Solver s2(d_tm);
  InputParser p3(&s2, d_symman.get());
  p3.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                               "input_parser_black");
  // logic is automatically set on the solver
  ASSERT_EQ(s2.isLogicSet(), true);
  ASSERT_EQ(s2.getLogic(), "QF_LIA");
  // we cannot set the logic since it has already been set
  ASSERT_THROW(parseLogicCommand(p3, "QF_LRA"), ParserException);

  // using a solver with the same logic is allowed
  Solver s3(d_tm);
  s3.setLogic("QF_LIA");
  InputParser p4(&s3, d_symman.get());
  p4.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                               "input_parser_black");

  // using a solver with a different logic is not allowed
  Solver s4(d_tm);
  s4.setLogic("QF_LRA");
  InputParser p5(&s4, d_symman.get());
  ASSERT_THROW(p5.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                            "input_parser_black"),
               CVC5ApiException);
}

TEST_F(TestInputParserBlack, ParserExceptions)
{
  ParserException defaultConstructor;
  std::string message = "error";
  const char* cMessage = "error";
  std::string filename = "file.smt2";
  ParserException stringConstructor(message);
  ParserException cStringConstructor(cMessage);
  ParserException exception(message, filename, 10, 11);
  std::stringstream ss;
  exception.toStream(ss);
  ASSERT_EQ(message, exception.getMessage());
  ASSERT_EQ(message, exception.getMessage());
  ASSERT_EQ(filename, exception.getFilename());
  ASSERT_EQ(10, exception.getLine());
  ASSERT_EQ(11, exception.getColumn());

  ParserEndOfFileException eofDefault;
  ParserEndOfFileException eofString(message);
  ParserEndOfFileException eofCMessage(cMessage);
  ParserEndOfFileException eof(message, filename, 10, 11);
}


TEST_F(TestInputParserBlack, incrementalSetString)
{
  InputParser p(d_solver.get(), d_symman.get());
  Command cmd;
  std::stringstream out;
  std::vector<std::string> stringVec;
  stringVec.push_back("(set-logic ALL)");
  stringVec.push_back("(push)");
  stringVec.push_back("(declare-fun x () Int)");
  stringVec.push_back("(pop)");
  stringVec.push_back("(declare-fun x () Int)");
  for (size_t i=0; i<stringVec.size(); i++)
  {
    p.setStringInput(modes::InputLanguage::SMT_LIB_2_6,
                    stringVec[i],
                    "input_parser_black");
    cmd = p.nextCommand();
    ASSERT_NE(cmd.isNull(), true);
    ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  }
  ASSERT_EQ(out.str().empty(), true);
}

TEST_F(TestInputParserBlack, getDeclaredTermsAndSorts)
{
  InputParser p(d_solver.get(), d_symman.get());
  Command cmd;
  std::stringstream out;
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  p.appendIncrementalStringInput("(set-logic ALL)");
  p.appendIncrementalStringInput("(declare-sort U 0)");
  p.appendIncrementalStringInput("(declare-fun x () U)");
  for (size_t i = 0; i < 3; i++)
  {
    cmd = p.nextCommand();
    ASSERT_NE(cmd.isNull(), true);
    ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  }
  std::vector<Sort> sorts = d_symman->getDeclaredSorts();
  std::vector<Term> terms = d_symman->getDeclaredTerms();
  ASSERT_EQ(sorts.size(), 1);
  ASSERT_EQ(terms.size(), 1);
  ASSERT_EQ(terms[0].getSort(), sorts[0]);
}

}  // namespace test
}  // namespace cvc5::internal
