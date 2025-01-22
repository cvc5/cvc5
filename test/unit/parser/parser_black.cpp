/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::parser::InputParser for SMT-LIbv2 inputs.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <sstream>

#include "base/output.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include <cvc5/cvc5_parser.h>
#include "test.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestParserBlack : public TestInternal
{
 protected:
  TestParserBlack(modes::InputLanguage lang) : d_lang(lang) {}

  virtual ~TestParserBlack() {}

  void SetUp() override
  {
    TestInternal::SetUp();
    d_symman.reset(nullptr);
    d_solver.reset(new cvc5::Solver(d_tm));
    d_solver->setOption("parse-only", "true");
  }

  void TearDown() override
  {
    d_symman.reset(nullptr);
    d_solver.reset(nullptr);
  }

  /* Set up declaration context for expr inputs */
  void setupContext(InputParser& parser)
  {
    std::stringstream ss;
    ss << "(set-logic ALL)" << std::endl;
    ss << "(declare-fun a () Bool)" << std::endl;
    ss << "(declare-fun b () Bool)" << std::endl;
    ss << "(declare-fun c () Bool)" << std::endl;
    ss << "(declare-sort t 0)" << std::endl;
    ss << "(declare-sort u 0)" << std::endl;
    ss << "(declare-sort v 0)" << std::endl;
    ss << "(declare-fun f (t) u)" << std::endl;
    ss << "(declare-fun g (u) v)" << std::endl;
    ss << "(declare-fun h (v) t)" << std::endl;
    ss << "(declare-fun x () t)" << std::endl;
    ss << "(declare-fun y () u)" << std::endl;
    ss << "(declare-fun z () v)" << std::endl;
    parser.setStreamInput(
        modes::InputLanguage::SMT_LIB_2_6, ss, "parser_black");
    Command cmd;
    std::stringstream tmp;
    while (true)
    {
      cmd = parser.nextCommand();
      if (cmd.isNull())
      {
        break;
      }
      cmd.invoke(d_solver.get(), d_symman.get(), tmp);
    }
  }

  void tryGoodInput(const std::string goodInput)
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_symman.reset(new SymbolManager(d_tm));
    InputParser parser(d_solver.get(), d_symman.get());
    std::stringstream ss;
    ss << goodInput;
    parser.setStreamInput(
        modes::InputLanguage::SMT_LIB_2_6, ss, "parser_black");
    ASSERT_FALSE(parser.done());
    Command cmd;
    std::stringstream tmp;
    while (true)
    {
      cmd = parser.nextCommand();
      if (cmd.isNull())
      {
        break;
      }
      Trace("parser") << "Parsed command: " << cmd << std::endl;
      cmd.invoke(d_solver.get(), d_symman.get(), tmp);
    }

    ASSERT_TRUE(parser.done());
  }

  void tryBadInput(const std::string badInput, bool strictMode = false)
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_solver->setOption("strict-parsing", strictMode ? "true" : "false");
    d_symman.reset(new SymbolManager(d_tm));
    InputParser parser(d_solver.get(), d_symman.get());
    std::stringstream ss;
    ss << badInput;
    parser.setStreamInput(d_lang, ss, "parser_black");
    ASSERT_THROW(
        {
          Command cmd;
          std::stringstream tmp;
          while (true)
          {
            cmd = parser.nextCommand();
            if (cmd.isNull())
            {
              break;
            }
            Trace("parser") << "Parsed command: " << cmd << std::endl;
            cmd.invoke(d_solver.get(), d_symman.get(), tmp);
          }
          std::cout << "\nBad input succeeded:\n" << badInput << std::endl;
        },
        ParserException);
  }

  void tryGoodExpr(const std::string goodExpr)
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_symman.reset(new SymbolManager(d_tm));
    InputParser parser(d_solver.get(), d_symman.get());
    setupContext(parser);

    std::stringstream ss;
    ss << goodExpr;
    parser.setStreamInput(d_lang, ss, "parser_black");

    ASSERT_FALSE(parser.done());
    cvc5::Term e = parser.nextTerm();
    ASSERT_FALSE(e.isNull());
    e = parser.nextTerm();
    ASSERT_TRUE(parser.done());
    ASSERT_TRUE(e.isNull());
  }

  /**
   * NOTE: The check implemented here may fail if a bad expression
   * expression string has a prefix that is parseable as a good
   * expression. E.g., the bad SMT v2 expression "#b10@@@@@@" will
   * actually return the bit-vector 10 and ignore the tail of the
   * input. It's more trouble than it's worth to check that the whole
   * input was consumed here, so just be careful to avoid valid
   * prefixes in tests.
   */
  void tryBadExpr(const std::string badExpr, bool strictMode = false)
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_solver->setOption("strict-parsing", strictMode ? "true" : "false");
    d_symman.reset(new SymbolManager(d_tm));
    InputParser parser(d_solver.get(), d_symman.get());
    setupContext(parser);
    std::stringstream ss;
    ss << badExpr;
    parser.setStreamInput(d_lang, ss, "parser_black");
    ASSERT_FALSE(parser.done());
    ASSERT_THROW(cvc5::Term e = parser.nextTerm();
                 std::cout << std::endl
                           << "Bad expr succeeded." << std::endl
                           << "Input: <<" << badExpr << ">>" << std::endl
                           << "Output: <<" << e << ">>" << std::endl;
                 , ParserException);
  }

  modes::InputLanguage d_lang;
  cvc5::TermManager d_tm;
  std::unique_ptr<cvc5::Solver> d_solver;
  std::unique_ptr<SymbolManager> d_symman;
};

/* -------------------------------------------------------------------------- */

class TestParserBlackSmt2InputParser : public TestParserBlack
{
 protected:
  TestParserBlackSmt2InputParser()
      : TestParserBlack(modes::InputLanguage::SMT_LIB_2_6)
  {
  }
};

TEST_F(TestParserBlackSmt2InputParser, good_inputs)
{
  tryGoodInput("");  // empty string is OK
  tryGoodInput("(set-logic QF_UF)");
  tryGoodInput("(set-info :notes |This is a note, take note!|)");
  tryGoodInput("(set-logic QF_UF) (assert true)");
  tryGoodInput("(check-sat)");
  tryGoodInput("(exit)");
  tryGoodInput("(set-logic QF_UF) (assert false) (check-sat)");
  tryGoodInput(
      "(set-logic QF_UF) (declare-fun a () Bool) "
      "(declare-fun b () Bool)");
  tryGoodInput(
      "(set-logic QF_UF) (declare-fun a () Bool) "
      "(declare-fun b () Bool) (assert (=> (and (=> a b) a) b))");
  tryGoodInput(
      "(set-logic QF_UF) (declare-sort a 0) "
      "(declare-fun f (a) a) (declare-fun x () a) "
      "(assert (= (f x) x))");
  tryGoodInput(
      "(set-logic QF_UF) (declare-sort a 0) "
      "(declare-fun x () a) (declare-fun y () a) "
      "(assert (= (ite true x y) x))");
  tryGoodInput(";; nothing but a comment");
  tryGoodInput("; a comment\n(check-sat ; goodbye\n)");
}

TEST_F(TestParserBlackSmt2InputParser, bad_inputs)
{
  // competition builds don't do any checking
#ifndef CVC5_COMPETITION_MODE
  // no arguments
  tryBadInput("(assert)");
  // illegal character in symbol
  tryBadInput("(set-info :notes |Symbols can't contain the | character|)");
  // check-sat should not have an argument
  tryBadInput("(set-logic QF_UF) (check-sat true)", true);
  // no argument
  tryBadInput("(declare-sort a)");
  // double declaration
  tryBadInput("(declare-sort a 0) (declare-sort a 0)");
  // should be "(declare-fun p () Bool)"
  tryBadInput("(set-logic QF_UF) (declare-fun p Bool)");
  // strict mode
  // no set-logic, core theory symbol "true" undefined
  tryBadInput("(assert true)", true);
  // core theory symbol "Bool" undefined
  tryBadInput("(declare-fun p Bool)", true);
#endif
}

TEST_F(TestParserBlackSmt2InputParser, good_exprs)
{
  tryGoodExpr("(and a b)");
  tryGoodExpr("(or (and a b) c)");
  tryGoodExpr("(=> (and (=> a b) a) b)");
  tryGoodExpr("(and (= a b) (not a))");
  tryGoodExpr("(= (xor a b) (and (or a b) (not (and a b))))");
  tryGoodExpr("(ite a (f x) y)");
  tryGoodExpr("1");
  tryGoodExpr("0");
  tryGoodExpr("1.5");
  tryGoodExpr("#xfab09c7");
  tryGoodExpr("#b0001011");
  tryGoodExpr("(* 5 1)");
}

TEST_F(TestParserBlackSmt2InputParser, bad_exprs)
{
// competition builds don't do any checking
#ifndef CVC5_COMPETITION_MODE
  tryBadExpr("(and)");                     // wrong arity
  tryBadExpr("(and a b");                  // no closing paren
  tryBadExpr("(a and b)");                 // infix
  tryBadExpr("(implies a b)");             // no implies in v2
  tryBadExpr("(iff a b)");                 // no iff in v2
  tryBadExpr("(OR (AND a b) c)");          // wrong case
  tryBadExpr("(a IMPLIES b)");             // infix AND wrong case
  tryBadExpr("(not a b)");                 // wrong arity
  tryBadExpr("not a");                     // needs parens
  tryBadExpr("(ite a x)");                 // wrong arity
  tryBadExpr("(if_then_else a (f x) y)");  // no if_then_else in v2
  tryBadExpr("(a b)");                     // using non-function as function
  tryBadExpr(".5");  // rational constants must have integer prefix
  tryBadExpr("1.");  // rational constants must have fractional suffix
  tryBadExpr("#x");  // hex constants must have at least one digit
  tryBadExpr("#b");  // ditto binary constants
  tryBadExpr("#xg0f");
  tryBadExpr("#b9");
  // Bad strict exprs
  tryBadExpr("(and a)", true);   // no unary and's
  tryBadExpr("(or a)", true);    // no unary or's
  tryBadExpr("(* 5 01)", true);  // '01' is not a valid integer constant
#endif
}
}  // namespace test
}  // namespace cvc5::internal
