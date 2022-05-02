/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Christopher L. Conway, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::parser::Parser for CVC and SMT-LIbv2 inputs.
 */

#include <sstream>

#include "api/cpp/cvc5.h"
#include "base/output.h"
#include "expr/symbol_manager.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/smt2/smt2.h"
#include "smt/command.h"
#include "test.h"

namespace cvc5::internal {

using namespace parser;

namespace test {

class TestParserBlackParser : public TestInternal
{
 protected:
  TestParserBlackParser(const std::string& lang) : d_lang(lang) {}

  virtual ~TestParserBlackParser() {}

  void SetUp() override
  {
    TestInternal::SetUp();
    d_symman.reset(nullptr);
    d_solver.reset(new cvc5::Solver());
    d_solver->setOption("parse-only", "true");
  }

  void TearDown() override
  {
    d_symman.reset(nullptr);
    d_solver.reset(nullptr);
  }

  /* Set up declaration context for expr inputs */
  void setupContext(Parser& parser)
  {
    /* a, b, c: BOOLEAN */
    parser.bindVar("a", d_solver.get()->getBooleanSort());
    parser.bindVar("b", d_solver.get()->getBooleanSort());
    parser.bindVar("c", d_solver.get()->getBooleanSort());
    /* t, u, v: TYPE */
    cvc5::Sort t = parser.mkSort("t");
    cvc5::Sort u = parser.mkSort("u");
    cvc5::Sort v = parser.mkSort("v");
    /* f : t->u; g: u->v; h: v->t; */
    parser.bindVar("f", d_solver.get()->mkFunctionSort({t}, u));
    parser.bindVar("g", d_solver.get()->mkFunctionSort({u}, v));
    parser.bindVar("h", d_solver.get()->mkFunctionSort({v}, t));
    /* x:t; y:u; z:v; */
    parser.bindVar("x", t);
    parser.bindVar("y", u);
    parser.bindVar("z", v);
  }

  void tryGoodInput(const std::string goodInput)
  {
    d_symman.reset(new SymbolManager(d_solver.get()));
    std::unique_ptr<Parser> parser(
        ParserBuilder(d_solver.get(), d_symman.get(), true)
            .withInputLanguage(d_lang)
            .build());
    parser->setInput(Input::newStringInput(d_lang, goodInput, "test"));
    ASSERT_FALSE(parser->done());
    Command* cmd;
    while ((cmd = parser->nextCommand()) != NULL)
    {
      Trace("parser") << "Parsed command: " << (*cmd) << std::endl;
      delete cmd;
    }

    ASSERT_TRUE(parser->done());
  }

  void tryBadInput(const std::string badInput, bool strictMode = false)
  {
    d_symman.reset(new SymbolManager(d_solver.get()));
    std::unique_ptr<Parser> parser(
        ParserBuilder(d_solver.get(), d_symman.get(), true)
            .withInputLanguage(d_lang)
            .withStrictMode(strictMode)
            .build());
    parser->setInput(Input::newStringInput(d_lang, badInput, "test"));
    ASSERT_THROW(
        {
          Command* cmd;
          while ((cmd = parser->nextCommand()) != NULL)
          {
            Trace("parser") << "Parsed command: " << (*cmd) << std::endl;
            delete cmd;
          }
          std::cout << "\nBad input succeeded:\n" << badInput << std::endl;
        },
        ParserException);
  }

  void tryGoodExpr(const std::string goodExpr)
  {
    d_symman.reset(new SymbolManager(d_solver.get()));
    std::unique_ptr<Parser> parser(
        ParserBuilder(d_solver.get(), d_symman.get(), true)
            .withInputLanguage(d_lang)
            .build());
    parser->setInput(Input::newStringInput(d_lang, goodExpr, "test"));
    if (d_lang == "LANG_SMTLIB_V2_6")
    {
      /* Use QF_LIA to make multiplication ("*") available */
      std::unique_ptr<Command> cmd(
          static_cast<Smt2*>(parser.get())->setLogic("QF_LIA"));
    }

    ASSERT_FALSE(parser->done());
    setupContext(*parser);
    ASSERT_FALSE(parser->done());
    cvc5::Term e = parser->nextExpression();
    ASSERT_FALSE(e.isNull());
    e = parser->nextExpression();
    ASSERT_TRUE(parser->done());
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
    d_symman.reset(new SymbolManager(d_solver.get()));
    std::unique_ptr<Parser> parser(
        ParserBuilder(d_solver.get(), d_symman.get(), true)
            .withInputLanguage(d_lang)
            .withStrictMode(strictMode)
            .build());
    parser->setInput(Input::newStringInput(d_lang, badExpr, "test"));
    setupContext(*parser);
    ASSERT_FALSE(parser->done());
    ASSERT_THROW(cvc5::Term e = parser->nextExpression();
                 std::cout << std::endl
                           << "Bad expr succeeded." << std::endl
                           << "Input: <<" << badExpr << ">>" << std::endl
                           << "Output: <<" << e << ">>" << std::endl;
                 , ParserException);
  }

  std::string d_lang;
  std::unique_ptr<cvc5::Solver> d_solver;
  std::unique_ptr<SymbolManager> d_symman;
};

/* -------------------------------------------------------------------------- */

class TestParserBlackSmt2Parser : public TestParserBlackParser
{
 protected:
  TestParserBlackSmt2Parser() : TestParserBlackParser("LANG_SMTLIB_V2_6") {}
};

TEST_F(TestParserBlackSmt2Parser, good_inputs)
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

TEST_F(TestParserBlackSmt2Parser, bad_inputs)
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

TEST_F(TestParserBlackSmt2Parser, good_exprs)
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

TEST_F(TestParserBlackSmt2Parser, bad_exprs)
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
