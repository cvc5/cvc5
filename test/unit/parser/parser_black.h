/*********************                                                        */
/*! \file parser_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::parser::Parser, including CVC, SMT and
 ** SMT v2 inputs.
 **
 ** Black box testing of CVC4::parser::Parser, including CVC, SMT, and
 ** SMT v2 inputs.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "api/cvc4cpp.h"
#include "base/output.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/options.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "parser/smt2/smt2.h"
#include "smt/command.h"


using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::language::input;
using namespace std;

class ParserBlack
{
 protected:
  Options d_options;

  /* Set up declaration context for expr inputs */
  virtual void setupContext(Parser& parser) {
    /* a, b, c: BOOLEAN */
    parser.bindVar("a", d_solver->getBooleanSort());
    parser.bindVar("b", d_solver->getBooleanSort());
    parser.bindVar("c", d_solver->getBooleanSort());
    /* t, u, v: TYPE */
    api::Sort t = parser.mkSort("t");
    api::Sort u = parser.mkSort("u");
    api::Sort v = parser.mkSort("v");
    /* f : t->u; g: u->v; h: v->t; */
    parser.bindVar("f", d_solver->mkFunctionSort(t, u));
    parser.bindVar("g", d_solver->mkFunctionSort(u, v));
    parser.bindVar("h", d_solver->mkFunctionSort(v, t));
    /* x:t; y:u; z:v; */
    parser.bindVar("x", t);
    parser.bindVar("y", u);
    parser.bindVar("z", v);
  }

  void tryGoodInput(const string goodInput)
  {
    try
    {
      //        Debug.on("parser");
      //         Debug.on("parser-extra");
      //        cerr << "Testing good input: <<" << goodInput << ">>" << endl;
      //        istringstream stream(goodInputs[i]);
      Parser* parser = ParserBuilder(d_solver.get(), "test")
                           .withStringInput(goodInput)
                           .withOptions(d_options)
                           .withInputLanguage(d_lang)
                           .build();
      TS_ASSERT(!parser->done());
      Command* cmd;
      while ((cmd = parser->nextCommand()) != NULL)
      {
        Debug("parser") << "Parsed command: " << (*cmd) << endl;
        delete cmd;
      }

      TS_ASSERT(parser->done());
      delete parser;
      //        Debug.off("parser");
      //        Debug.off("parser-extra");
    }
    catch (Exception& e)
    {
      cout << "\nGood input failed:\n" << goodInput << endl << e << endl;
      //        Debug.off("parser");
      throw;
    }
  }

  void tryBadInput(const string badInput, bool strictMode = false)
  {
    //      cerr << "Testing bad input: '" << badInput << "'\n";
    //      Debug.on("parser");

    Parser* parser = ParserBuilder(d_solver.get(), "test")
                         .withStringInput(badInput)
                         .withOptions(d_options)
                         .withInputLanguage(d_lang)
                         .withStrictMode(strictMode)
                         .build();
    TS_ASSERT_THROWS(
        {
          Command* cmd;
          while ((cmd = parser->nextCommand()) != NULL)
          {
            Debug("parser") << "Parsed command: " << (*cmd) << endl;
            delete cmd;
          }
          cout << "\nBad input succeeded:\n" << badInput << endl;
        },
        const ParserException&);
    //      Debug.off("parser");
    delete parser;
  }

  void tryGoodExpr(const string goodExpr)
  {
    //    Debug.on("parser");
    //    Debug.on("parser-extra");
    try
    {
      //        cerr << "Testing good expr: '" << goodExpr << "'\n";
      // Debug.on("parser");
      //        istringstream stream(context + goodBooleanExprs[i]);

      Parser* parser = ParserBuilder(d_solver.get(), "test")
                           .withStringInput(goodExpr)
                           .withOptions(d_options)
                           .withInputLanguage(d_lang)
                           .build();

      if (d_lang == LANG_SMTLIB_V2)
      {
        // Use QF_LIA to make multiplication ("*") available
        std::unique_ptr<Command> cmd(
            static_cast<Smt2*>(parser)->setLogic("QF_LIA"));
      }

      TS_ASSERT(!parser->done());
      setupContext(*parser);
      TS_ASSERT(!parser->done());
      api::Term e = parser->nextExpression();
      TS_ASSERT(!e.isNull());
      e = parser->nextExpression();
      TS_ASSERT(parser->done());
      TS_ASSERT(e.isNull());
      delete parser;
    }
    catch (Exception& e)
    {
      cout << endl
           << "Good expr failed." << endl
           << "Input: <<" << goodExpr << ">>" << endl
           << "Output: <<" << e << ">>" << endl;
      throw;
    }
  }

  /* NOTE: The check implemented here may fail if a bad expression
   * expression string has a prefix that is parseable as a good
   * expression. E.g., the bad SMT v2 expression "#b10@@@@@@" will
   * actually return the bit-vector 10 and ignore the tail of the
   * input. It's more trouble than it's worth to check that the whole
   * input was consumed here, so just be careful to avoid valid
   * prefixes in tests.
   */
  void tryBadExpr(const string badExpr, bool strictMode = false)
  {
    //    Debug.on("parser");
    //    Debug.on("parser-extra");
    //      cout << "Testing bad expr: '" << badExpr << "'\n";

    Parser* parser = ParserBuilder(d_solver.get(), "test")
                         .withStringInput(badExpr)
                         .withOptions(d_options)
                         .withInputLanguage(d_lang)
                         .withStrictMode(strictMode)
                         .build();
    setupContext(*parser);
    TS_ASSERT(!parser->done());
    TS_ASSERT_THROWS(api::Term e = parser->nextExpression();
                     cout << endl
                          << "Bad expr succeeded." << endl
                          << "Input: <<" << badExpr << ">>" << endl
                          << "Output: <<" << e << ">>" << endl;
                     , const ParserException&);
    delete parser;
    //    Debug.off("parser");
  }

  ParserBlack(InputLanguage lang) :
    d_lang(lang) {
  }

  virtual ~ParserBlack() {}

  void setUp()
  {
    d_options.set(options::parseOnly, true);
    d_solver.reset(new api::Solver(&d_options));
  }

  void tearDown() {
  }

 private:
  InputLanguage d_lang;
  std::unique_ptr<api::Solver> d_solver;

}; /* class ParserBlack */

class Cvc4ParserTest : public CxxTest::TestSuite, public ParserBlack {
  typedef ParserBlack super;

public:
  Cvc4ParserTest() : ParserBlack(LANG_CVC4) { }

  void setUp() override { super::setUp(); }

  void tearDown() override { super::tearDown(); }

  void testGoodCvc4Inputs() {
    tryGoodInput(""); // empty string is OK
    tryGoodInput(";"); // no command is OK
    tryGoodInput("ASSERT TRUE;");
    tryGoodInput("QUERY TRUE;");
    tryGoodInput("CHECKSAT FALSE;");
    tryGoodInput("a, b : BOOLEAN;");
    tryGoodInput("a, b : BOOLEAN; QUERY (a => b) AND a => b;");
    tryGoodInput("T, U : TYPE; f : T -> U; x : T; y : U; CHECKSAT f(x) = y;");
    tryGoodInput("T : TYPE = BOOLEAN; x : T; CHECKSAT x;");
    tryGoodInput("a : ARRAY INT OF REAL; ASSERT (a WITH [1] := 0.0)[1] = a[0];");
    tryGoodInput("b : BITVECTOR(3); ASSERT b = 0bin101;");
    tryGoodInput("T : TYPE = BOOLEAN; x : T; CHECKSAT x;");
    tryGoodInput("T : TYPE; x, y : T; a : BOOLEAN; QUERY (IF a THEN x ELSE y ENDIF) = x;");
    tryGoodInput("CHECKSAT 0bin0000 /= 0hex7;");
    tryGoodInput("%% nothing but a comment");
    tryGoodInput("% a comment\nASSERT TRUE; %a command\n% another comment");
    tryGoodInput("a : BOOLEAN; a: BOOLEAN;"); // double decl, but compatible
    tryGoodInput("a : INT = 5; a: INT;"); // decl after define, compatible
    tryGoodInput("a : TYPE; a : INT;"); // ok, sort and variable symbol spaces distinct
    tryGoodInput("a : TYPE; a : INT; b : a;"); // ok except a is both INT and sort `a'
    //tryGoodInput("a : [0..0]; b : [-5..5]; c : [-1..1]; d : [ _ .._];"); // subranges
    tryGoodInput("a : [ _..1]; b : [_.. 0]; c :[_..-1];");
    tryGoodInput("DATATYPE list = nil | cons(car:INT,cdr:list) END; DATATYPE cons = null END;");
    tryGoodInput("DATATYPE tree = node(data:list), list = cons(car:tree,cdr:list) | nil END;");
    //tryGoodInput("DATATYPE tree = node(data:[list,list,ARRAY tree OF list]), list = cons(car:ARRAY list OF tree,cdr:BITVECTOR(32)) END;");
    tryGoodInput(
        "DATATYPE trex = Foo | Bar END; DATATYPE tree = "
        "node(data:[list,list,ARRAY trex OF list]), list = cons(car:ARRAY list "
        "OF tree,cdr:BITVECTOR(32)) END;");
  }

  void testBadCvc4Inputs() {
// competition builds don't do any checking
#ifndef CVC4_COMPETITION_MODE
    tryBadInput("ASSERT;"); // no args
    tryBadInput("QUERY");
    tryBadInput("CHECKSAT");
    tryBadInput("a, b : boolean;"); // lowercase boolean isn't a type
    tryBadInput("0x : INT;"); // 0x isn't an identifier
    tryBadInput("a, b : BOOLEAN\nQUERY (a => b) AND a => b;"); // no semicolon after decl
    tryBadInput("ASSERT 0bin012 /= 0hex0;"); // bad binary literal
    tryBadInput("a, b: BOOLEAN; QUERY a(b);"); // non-function used as function
    tryBadInput("a : BOOLEAN; a: INT;"); // double decl, incompatible
    tryBadInput("A : TYPE; A: TYPE;"); // types can't be double-declared
    tryBadInput("a : INT; a: INT = 5;"); // can't define after decl
    tryBadInput("a : INT = 5; a: BOOLEAN;"); // decl w/ incompatible type
    tryBadInput("a : TYPE; a : INT; a : a;"); // ok except a is both INT and sort `a'
    //tryBadInput("a : [1..-1];"); // bad subrange
    //tryBadInput("a : [0. .0];"); // bad subrange
    //tryBadInput("a : [..0];"); // bad subrange
    //tryBadInput("a : [0.0];"); // bad subrange
    tryBadInput("DATATYPE list = nil | cons(car:INT,cdr:list) END; DATATYPE list = nil | cons(car:INT,cdr:list) END;");
    tryBadInput("DATATYPE list = nil | cons(car:INT,cdr:list) END; DATATYPE list2 = nil END;");
    tryBadInput("DATATYPE tree = node(data:(list,list,ARRAY trex OF list)), list = cons(car:ARRAY list OF tree,cdr:BITVECTOR(32)) END;");
#endif /* ! CVC4_COMPETITION_MODE */
  }

  void testGoodCvc4Exprs() {
    tryGoodExpr("a AND b");
    tryGoodExpr("a AND b OR c");
    tryGoodExpr("(a => b) AND a => b");
    tryGoodExpr("(a <=> b) AND (NOT a)");
    tryGoodExpr("(a XOR b) <=> (a OR b) AND (NOT (a AND b))");
  }

  void testBadCvc4Exprs() {
// competition builds don't do any checking
#ifndef CVC4_COMPETITION_MODE
    tryBadInput("a AND"); // wrong arity
    tryBadInput("AND(a,b)"); // not infix
    tryBadInput("(OR (AND a b) c)"); // not infix
    tryBadInput("a IMPLIES b"); // should be =>
    tryBadInput("a NOT b"); // wrong arity, not infix
    tryBadInput("a and b"); // wrong case
#endif /* ! CVC4_COMPETITION_MODE */
  }
};/* class Cvc4ParserTest */

class Smt2ParserTest : public CxxTest::TestSuite, public ParserBlack {
  typedef ParserBlack super;

public:
  Smt2ParserTest() : ParserBlack(LANG_SMTLIB_V2) { }

  void setUp() override { super::setUp(); }

  void tearDown() override { super::tearDown(); }

  void setupContext(Parser& parser) override
  {
    super::setupContext(parser);
  }

  void testGoodSmt2Inputs() {
    tryGoodInput(""); // empty string is OK
    tryGoodInput("(set-logic QF_UF)");
    tryGoodInput("(set-info :notes |This is a note, take note!|)");
    tryGoodInput("(set-logic QF_UF) (assert true)");
    tryGoodInput("(check-sat)");
    tryGoodInput("(exit)");
    tryGoodInput("(set-logic QF_UF) (assert false) (check-sat)");
    tryGoodInput("(set-logic QF_UF) (declare-fun a () Bool) "
                 "(declare-fun b () Bool)");
    tryGoodInput("(set-logic QF_UF) (declare-fun a () Bool) "
                 "(declare-fun b () Bool) (assert (=> (and (=> a b) a) b))");
    tryGoodInput("(set-logic QF_UF) (declare-sort a 0) "
                 "(declare-fun f (a) a) (declare-fun x () a) "
                 "(assert (= (f x) x))");
    tryGoodInput("(set-logic QF_UF) (declare-sort a 0) "
                 "(declare-fun x () a) (declare-fun y () a) "
                 "(assert (= (ite true x y) x))");
    tryGoodInput(";; nothing but a comment");
    tryGoodInput("; a comment\n(check-sat ; goodbye\n)");
  }

  void testBadSmt2Inputs() {
// competition builds don't do any checking
#ifndef CVC4_COMPETITION_MODE
    tryBadInput("(assert)"); // no args
    tryBadInput("(set-info :notes |Symbols can't contain the | character|)");
    tryBadInput("(set-logic QF_UF) (check-sat true)", true); // check-sat shouldn't have an arg
    tryBadInput("(declare-sort a)"); // no arg
    tryBadInput("(declare-sort a 0) (declare-sort a 0)"); // double decl
    tryBadInput("(set-logic QF_UF) (declare-fun p Bool)"); // should be "p () Bool"
    // strict mode
    tryBadInput("(assert true)", true); // no set-logic, core theory symbol "true" undefined
    tryBadInput("(declare-fun p Bool)", true); // core theory symbol "Bool" undefined
#endif /* ! CVC4_COMPETITION_MODE */
  }

  void testGoodSmt2Exprs() {
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
    tryGoodExpr("(* 5 01)"); // '01' is OK in non-strict mode
  }

  void testBadSmt2Exprs() {
// competition builds don't do any checking
#ifndef CVC4_COMPETITION_MODE
    tryBadExpr("(and)"); // wrong arity
    tryBadExpr("(and a b"); // no closing paren
    tryBadExpr("(a and b)"); // infix
    tryBadExpr("(implies a b)"); // no implies in v2
    tryBadExpr("(iff a b)"); // no iff in v2
    tryBadExpr("(OR (AND a b) c)"); // wrong case
    tryBadExpr("(a IMPLIES b)"); // infix AND wrong case
    tryBadExpr("(not a b)"); // wrong arity
    tryBadExpr("not a"); // needs parens
    tryBadExpr("(ite a x)"); // wrong arity
    tryBadExpr("(if_then_else a (f x) y)"); // no if_then_else in v2
    tryBadExpr("(a b)"); // using non-function as function
    tryBadExpr(".5"); // rational constants must have integer prefix
    tryBadExpr("1."); // rational constants must have fractional suffix
    tryBadExpr("#x"); // hex constants must have at least one digit
    tryBadExpr("#b"); // ditto binary constants
    tryBadExpr("#xg0f");
    tryBadExpr("#b9");
    // Bad strict exprs
    tryBadExpr("(and a)", true); // no unary and's
    tryBadExpr("(or a)", true);  // no unary or's
    tryBadExpr("(* 5 01)", true); // '01' is not a valid integer constant
#endif /* ! CVC4_COMPETITION_MODE */
  }
};/* class Smt2ParserTest */
