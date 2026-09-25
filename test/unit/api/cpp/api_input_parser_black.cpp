/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include <unordered_set>

#include "base/output.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "test_parser.h"

using namespace cvc5::parser;

namespace cvc5::internal {
namespace test {

class TestApiBlackInputParser : public TestParser
{
 protected:
  TestApiBlackInputParser() {}
  virtual ~TestApiBlackInputParser() {}

  Command parseLogicCommand(InputParser& p, const std::string& logic)
  {
    p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                "input_parser_black");
    std::stringstream ss;
    ss << "(set-logic " << logic << ")" << std::endl;
    p.appendIncrementalStringInput(ss.str());
    return p.nextCommand();
  }

  void parseCommands(InputParser& p, const std::string& input)
  {
    p.setStringInput(modes::InputLanguage::SMT_LIB_2_6, input, "macros");
    std::stringstream out;
    for (Command cmd = p.nextCommand(); !cmd.isNull(); cmd = p.nextCommand())
    {
      cmd.invoke(d_solver.get(), d_symman.get(), out);
    }
    ASSERT_EQ(out.str(), "");
  }

  Term parseTerm(InputParser& p, const std::string& input)
  {
    p.setStringInput(modes::InputLanguage::SMT_LIB_2_6, input, "macros");
    return p.nextTerm();
  }
};

TEST_F(TestApiBlackInputParser, defineFunMacros)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-logic ALL)"
                "(declare-const a Int)"
                "(define-fun f ((x Int)) Int (+ x 1))"
                "(define-fun g ((x Int)) Int (f (f x)))"
                "(define-fun c () Int 2)"
                "(define-const d Int (f c))");
  ASSERT_EQ(parseTerm(p, "f").getKind(), Kind::LAMBDA);
  ASSERT_EQ(parseTerm(p, "(g a)"), parseTerm(p, "(+ (+ a 1) 1)"));
  ASSERT_EQ(parseTerm(p, "d"), parseTerm(p, "(+ 2 1)"));
  ASSERT_EQ(parseTerm(p, "((as f Int) a)"), parseTerm(p, "(+ a 1)"));
  // Definitions belong to the symbol manager, including when it is shared.
  InputParser p2(d_solver.get(), d_symman.get());
  ASSERT_EQ(parseTerm(p2, "(f a)"), parseTerm(p, "(+ a 1)"));
  ASSERT_TRUE(d_solver->getAssertions().empty());
}

TEST_F(TestApiBlackInputParser, defineFunMacrosCapture)
{
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-option :parse-define-fun-macros true)"
                "(set-logic LIA)"
                "(define-fun p ((x Int)) Bool (forall ((y Int)) (= x y)))"
                "(define-fun q ((x Int)) Bool (forall ((x Int)) (= x 0)))");
  Term t = parseTerm(p, "(forall ((y Int)) (p y))");
  ASSERT_EQ(t.getKind(), Kind::FORALL);
  ASSERT_EQ(t[1].getKind(), Kind::FORALL);
  ASSERT_NE(t[0][0], t[1][0][0]);
  ASSERT_EQ(t[1][1][0], t[0][0]);
  ASSERT_EQ(t[1][1][1], t[1][0][0]);
  Term q = parseTerm(p, "(q 1)");
  ASSERT_EQ(q[1][0], q[0][0]);
  d_solver->assertFormula(d_tm.mkTerm(Kind::NOT, {t}));
  ASSERT_TRUE(d_solver->checkSat().isSat());
}

TEST_F(TestApiBlackInputParser, defineFunMacrosOverloading)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-logic ALL)"
                "(define-fun c () Int 0)"
                "(define-fun d () Int 0)"
                "(declare-const c Bool)"
                "(define-fun f ((x Int)) Int x)"
                "(declare-fun f (Bool) Bool)");
  ASSERT_EQ(parseTerm(p, "d"), d_tm.mkInteger(0));
  ASSERT_EQ(parseTerm(p, "(as c Int)"), d_tm.mkInteger(0));
  ASSERT_EQ(parseTerm(p, "(as c Bool)").getSort(), d_bool);
  ASSERT_EQ(parseTerm(p, "(f 1)"), d_tm.mkInteger(1));
  ASSERT_EQ(parseTerm(p, "(f false)").getKind(), Kind::APPLY_UF);
  // An overload for an alias in a popped scope must not remain active.
  parseCommands(p, "(push 1)(declare-const d Bool)(pop 1)");
  ASSERT_EQ(parseTerm(p, "d"), d_tm.mkInteger(0));
  ASSERT_THROW(parseTerm(p, "(as d Bool)"), ParserException);
}

TEST_F(TestApiBlackInputParser, defineFunMacrosScopes)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-logic ALL)(push 1)"
                "(define-fun local ((x Int)) Int (+ x 1))(pop 1)");
  ASSERT_THROW(parseTerm(p, "(local 0)"), ParserException);
  parseCommands(p, "(define-fun local ((x Int)) Int (+ x 2))");
  ASSERT_EQ(parseTerm(p, "(local 0)"), parseTerm(p, "(+ 0 2)"));
}

TEST_F(TestApiBlackInputParser, defineFunMacrosGlobalScopes)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-option :global-declarations true)(set-logic ALL)(push 1)"
                "(define-fun global ((x Int)) Int (+ x 2))(pop 1)");
  ASSERT_EQ(parseTerm(p, "(global 0)"), parseTerm(p, "(+ 0 2)"));
  parseCommands(p, "(reset-assertions)");
  ASSERT_EQ(parseTerm(p, "(global 0)"), parseTerm(p, "(+ 0 2)"));
  parseCommands(p,
                "(reset)(set-logic ALL)"
                "(define-fun after-reset ((x Int)) Int (+ x 2))");
  ASSERT_EQ(d_solver->getOption("parse-define-fun-macros"), "false");
  ASSERT_EQ(parseTerm(p, "after-reset").getKind(), Kind::CONSTANT);
}

TEST_F(TestApiBlackInputParser, defineFunMacrosTypeChecking)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-logic ALL)"
                "(define-fun unused ((x Int)) Int 0)"
                "(define-fun real-id ((x Real)) Real x)");
  ASSERT_THROW(parseTerm(p, "(unused true)"), ParserException);
  ASSERT_THROW(parseTerm(p, "(unused 1 2)"), ParserException);
  ASSERT_THROW(parseTerm(p, "(real-id 1)"), ParserException);
  ASSERT_EQ(parseTerm(p, "(real-id 1.0)"), d_tm.mkReal(1));
  p.setStringInput(modes::InputLanguage::SMT_LIB_2_6,
                   "(define-fun bad () Bool 0)",
                   "macros");
  Command cmd = p.nextCommand();
  std::stringstream out;
  cmd.invoke(d_solver.get(), d_symman.get(), out);
  ASSERT_NE(out.str().find("(error"), std::string::npos);
  ASSERT_THROW(parseTerm(p, "bad"), ParserException);
  p.setStringInput(modes::InputLanguage::SMT_LIB_2_6,
                   "(define-fun bad ((x Int) (x Int)) Int x)",
                   "macros");
  ASSERT_THROW(p.nextCommand(), ParserException);
}

TEST_F(TestApiBlackInputParser, defineFunMacrosHigherOrder)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-logic HO_ALL)"
                "(define-fun f ((x Int) (y Int)) Int (+ x y))"
                "(define-fun g ((__flatten_var_0 Int)) (-> Int Int)"
                "  (f __flatten_var_0))");
  ASSERT_EQ(parseTerm(p, "(f 1)").getKind(), Kind::LAMBDA);
  ASSERT_EQ(parseTerm(p, "(@ (f 1) 2)"), parseTerm(p, "(+ 1 2)"));
  ASSERT_EQ(parseTerm(p, "(g 1 2)"), parseTerm(p, "(+ 1 2)"));
}

TEST_F(TestApiBlackInputParser, defineFunMacrosProof)
{
  d_solver->setOption("parse-define-fun-macros", "true");
  d_solver->setOption("produce-proofs", "true");
  d_solver->setOption("check-proofs", "true");
  InputParser p(d_solver.get(), d_symman.get());
  parseCommands(p,
                "(set-logic QF_LIA)"
                "(declare-const a Int)"
                "(define-fun f ((x Int)) Int (+ x 1))"
                "(assert (< (f a) a))");
  ASSERT_EQ(d_solver->getAssertions(),
            std::vector<Term>{parseTerm(p, "(< (+ a 1) a)")});
  ASSERT_TRUE(d_solver->checkSat().isUnsat());
  std::vector<Proof> todo = d_solver->getProof();
  std::unordered_set<Proof> visited;
  while (!todo.empty())
  {
    Proof proof = todo.back();
    todo.pop_back();
    if (!visited.insert(proof).second)
    {
      continue;
    }
    ASSERT_NE(proof.getRule(), ProofRule::HO_CONG);
    if (proof.getRule() == ProofRule::DSL_REWRITE
        || proof.getRule() == ProofRule::THEORY_REWRITE)
    {
      ASSERT_NE(proof.getRewriteRule(), ProofRewriteRule::BETA_REDUCE);
    }
    std::vector<Proof> children = proof.getChildren();
    todo.insert(todo.end(), children.begin(), children.end());
  }
  std::string printed = d_solver->proofToString(d_solver->getProof()[0]);
  ASSERT_EQ(printed.find("lambda"), std::string::npos);
}

TEST_F(TestApiBlackInputParser, constructSymbolManager)
{
  (void)SymbolManager(d_tm);
}

TEST_F(TestApiBlackInputParser, getSolver)
{
  InputParser p(d_solver.get());
  ASSERT_EQ(p.getSolver(), d_solver.get());
}

TEST_F(TestApiBlackInputParser, getSymbolManager)
{
  InputParser p(d_solver.get());
  // a symbol manager is allocated
  ASSERT_NE(p.getSymbolManager(), nullptr);

  InputParser p2(d_solver.get(), d_symman.get());
  ASSERT_EQ(p2.getSymbolManager(), d_symman.get());
}

TEST_F(TestApiBlackInputParser, setFileInput)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(
      p.setFileInput(modes::InputLanguage::SMT_LIB_2_6, "nonexistent.smt2"),
      CVC5ApiException);
}

TEST_F(TestApiBlackInputParser, setStreamInput)
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

TEST_F(TestApiBlackInputParser, setAndAppendIncrementalStringInput)
{
  std::stringstream out;
  InputParser p(d_solver.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  ASSERT_EQ(p.done(), false);
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
  ASSERT_EQ(p.done(), false);
  cmd = p.nextCommand();
  ASSERT_TRUE(cmd.isNull());
  ASSERT_EQ(p.done(), true);
}

TEST_F(TestApiBlackInputParser, setAndAppendIncrementalStringInputInterleave)
{
  std::stringstream out;
  InputParser p(d_solver.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  ASSERT_EQ(p.done(), false);
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
  ASSERT_EQ(p.done(), false);
  cmd = p.nextCommand();
  ASSERT_TRUE(cmd.isNull());
  ASSERT_EQ(p.done(), true);
}

TEST_F(TestApiBlackInputParser, appendIncrementalNoSet)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(p.appendIncrementalStringInput("(set-logic ALL)"),
               CVC5ApiException);
}

TEST_F(TestApiBlackInputParser, setStringInput)
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

TEST_F(TestApiBlackInputParser, nextCommand)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(p.nextCommand(), CVC5ApiException);
  std::stringstream ss;
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "input_parser_black");
  Command cmd = p.nextCommand();
  ASSERT_EQ(cmd.isNull(), true);
}

TEST_F(TestApiBlackInputParser, nextCommandNoInput)
{
  InputParser p(d_solver.get());
  p.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                              "input_parser_black");
  Command cmd = p.nextCommand();
  ASSERT_EQ(cmd.isNull(), true);
  Term t = p.nextTerm();
  ASSERT_EQ(t.isNull(), true);
}

TEST_F(TestApiBlackInputParser, nextTerm)
{
  InputParser p(d_solver.get());
  ASSERT_THROW(p.nextTerm(), CVC5ApiException);
  std::stringstream ss;
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "input_parser_black");
  ASSERT_EQ(p.nextTerm().isNull(), true);
}

TEST_F(TestApiBlackInputParser, nextTerm2)
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

TEST_F(TestApiBlackInputParser, multipleParsers)
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

TEST_F(TestApiBlackInputParser, ParserExceptions)
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

TEST_F(TestApiBlackInputParser, incrementalSetString)
{
  InputParser p(d_solver.get(), d_symman.get());
  Command cmd;
  std::stringstream out;
  std::vector<std::string> strs{"(set-logic ALL)",
                                "(push)",
                                "(declare-fun x () Int)",
                                "(pop)",
                                "(declare-fun x () Int)"};
  for (size_t i = 0; i < strs.size(); i++)
  {
    p.setStringInput(
        modes::InputLanguage::SMT_LIB_2_6, strs[i], "input_parser_black");
    cmd = p.nextCommand();
    ASSERT_NE(cmd.isNull(), true);
    ASSERT_NO_THROW(cmd.invoke(d_solver.get(), d_symman.get(), out));
  }
  ASSERT_EQ(out.str().empty(), true);
}

TEST_F(TestApiBlackInputParser, getDeclaredTermsAndSorts)
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
