/*********************                                                        */
/** parser_white.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::parser::SmtParser.
 **/

#include <cxxtest/TestSuite.h>
//#include <string>
#include <sstream>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser_state.h"
#include "expr/command.h"
#include "util/output.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace std;


/************************** CVC test inputs ********************************/

const string goodCvc4Inputs[] = {
      "", // empty string is OK
      "ASSERT TRUE;",
      "QUERY TRUE;",
      "CHECKSAT FALSE;",
      "a, b : BOOLEAN;",
      "a, b : BOOLEAN; QUERY (a => b) AND a => b;",
      "T, U : TYPE; f : T -> U; x : T; CHECKSAT f(x) = x;",
      "T : TYPE; x, y : T; a : BOOLEAN; QUERY (IF a THEN x ELSE y ENDIF) = x;",
      "%% nothing but a comment",
      "% a comment\nASSERT TRUE; %a command\n% another comment",
  };

const int numGoodCvc4Inputs = sizeof(goodCvc4Inputs) / sizeof(string);


/* The following expressions are valid after setupContext. */
const string goodCvc4Exprs[] = {
    "a AND b",
    "a AND b OR c",
    "(a => b) AND a => b",
    "(a <=> b) AND (NOT a)",
    "(a XOR b) <=> (a OR b) AND (NOT (a AND b))"
};

const int numGoodCvc4Exprs = sizeof(goodCvc4Exprs) / sizeof(string);

const string badCvc4Inputs[] = {
      ";", // no command
      "ASSERT;", // no args
      "QUERY",
      "CHECKSAT",
      "a, b : boolean;", // lowercase boolean isn't a type
      "0x : INT;", // 0x isn't an identifier
      "a, b : BOOLEAN\nQUERY (a => b) AND a => b;", // no semicolon after decl
      "a : BOOLEAN; a: BOOLEAN;" // double decl
      "a, b: BOOLEAN; QUERY a(b);" // non-function used as function
  };

const int numBadCvc4Inputs = sizeof(badCvc4Inputs) / sizeof(string);

/* The following expressions are invalid even after setupContext. */
const string badCvc4Exprs[] = {
    "a AND", // wrong arity
    "AND(a,b)", // not infix
    "(OR (AND a b) c)", // not infix
    "a IMPLIES b", // should be =>
    "a NOT b", // wrong arity, not infix
    "a and b" // wrong case
};

const int numBadCvc4Exprs = sizeof(badCvc4Exprs) / sizeof(string);

/************************** SMT test inputs ********************************/

const string goodSmtInputs[] = {
    "", // empty string is OK
    "(benchmark foo :assumption true)",
    "(benchmark bar :formula true)",
    "(benchmark qux :formula false)",
    "(benchmark baz :extrapreds ( (a) (b) ) )",
    "(benchmark zab :extrapreds ( (a) (b) ) :formula (implies (and (implies a b) a) b))",
    "(benchmark zub :extrasorts (a) :extrafuns ( (f a a) (x a) )  :formula (= (f x) x))",
    "(benchmark fuz :extrasorts (a) :extrafuns ((x a) (y a)) :formula (= (ite true x y) x))",
    ";; nothing but a comment",
    "; a comment\n(benchmark foo ; hello\n  :formula true; goodbye\n)"
  };

const int numGoodSmtInputs = sizeof(goodSmtInputs) / sizeof(string);

/* The following expressions are valid after setupContext. */
const string goodSmtExprs[] = {
    "(and a b)",
    "(or (and a b) c)",
    "(implies (and (implies a b) a) b)",
    "(and (iff a b) (not a))",
    "(iff (xor a b) (and (or a b) (not (and a b))))",
    "(ite a (f x) y)",
    "(if_then_else a (f x) y)"
};

const int numGoodSmtExprs = sizeof(goodSmtExprs) / sizeof(string);

const string badSmtInputs[] = {
    "(benchmark foo)", // empty benchmark is not OK
    "(benchmark bar :assumption)", // no args
    "(benchmark bar :formula)",
    "(benchmark baz :extrapreds ( (a) (a) ) )", // double decl
    "(benchmark zub :extrasorts (a) :extrapreds (p a))" // (p a) needs parens
  };

const int numBadSmtInputs = sizeof(badSmtInputs) / sizeof(string);

/* The following expressions are invalid even after setupContext. */
const string badSmtExprs[] = {
    "(and)", // wrong arity
    "(and a b", // no closing paren
    "(a and b)", // infix
    "(OR (AND a b) c)", // wrong case
    "(a IMPLIES b)", // infix AND wrong case
    "(not a b)", // wrong arity
    "not a", // needs parens
    "(ite a x)", // wrong arity
    "(a b)" // using non-function as function
};

const int numBadSmtExprs = sizeof(badSmtExprs) / sizeof(string);

class ParserWhite : public CxxTest::TestSuite {
  ExprManager *d_exprManager;

  /* Set up declaration context for expr inputs */

  void setupContext(ParserState* parserState) {
    /* a, b, c: BOOLEAN */
    parserState->mkVar("a",d_exprManager->booleanType());
    parserState->mkVar("b",d_exprManager->booleanType());
    parserState->mkVar("c",d_exprManager->booleanType());
    /* t, u, v: TYPE */
    Type t = parserState->mkSort("t");
    Type u = parserState->mkSort("u");
    Type v = parserState->mkSort("v");
    /* f : t->u; g: u->v; h: v->t; */
    parserState->mkVar("f", d_exprManager->mkFunctionType(t,u));
    parserState->mkVar("g", d_exprManager->mkFunctionType(u,v));
    parserState->mkVar("h", d_exprManager->mkFunctionType(v,t));
    /* x:t; y:u; z:v; */
    parserState->mkVar("x",t);
    parserState->mkVar("y",u);
    parserState->mkVar("z",v);
  }

  void tryGoodInputs(InputLanguage d_lang, const string goodInputs[], int numInputs) {
    for(int i = 0; i < numInputs; ++i) {
      try {
//         Debug.on("parser");
//         Debug.on("parser-extra");
         Debug("test") << "Testing good input: '" << goodInputs[i] << "'\n";
//        istringstream stream(goodInputs[i]);
        Input* parser = Input::newStringInput(d_exprManager, d_lang, goodInputs[i], "test");
        TS_ASSERT( !parser->done() );
        Command* cmd;
        while((cmd = parser->parseNextCommand())) {
          // cout << "Parsed command: " << (*cmd) << endl;
        }
        TS_ASSERT( parser->parseNextCommand() == NULL );
        TS_ASSERT( parser->done() );
        delete parser;
//        Debug.off("parser");
//        Debug.off("parser-extra");
      } catch (Exception& e) {
        cout << "\nGood input failed:\n" << goodInputs[i] << endl
             << e << endl;
//        Debug.off("parser-extra");
        throw;
      }
    }
  }

  void tryBadInputs(InputLanguage d_lang, const string badInputs[], int numInputs) {
    for(int i = 0; i < numInputs; ++i) {
//      cout << "Testing bad input: '" << badInputs[i] << "'\n";
//      Debug.on("parser");
      Input* parser = Input::newStringInput(d_exprManager, d_lang, badInputs[i], "test");
      TS_ASSERT_THROWS
        ( while(parser->parseNextCommand());
          cout << "\nBad input succeeded:\n" << badInputs[i] << endl;,
          ParserException );
//      Debug.off("parser");
      delete parser;
    }
  }

  void tryGoodExprs(InputLanguage d_lang, const string goodBooleanExprs[], int numExprs) {
    // cout << "Using context: " << context << endl;
//    Debug.on("parser");
//    Debug.on("parser-extra");
    for(int i = 0; i < numExprs; ++i) {
      try {
        // cout << "Testing good expr: '" << goodBooleanExprs[i] << "'\n";
        // Debug.on("parser");
//        istringstream stream(context + goodBooleanExprs[i]);
        Input* input = Input::newStringInput(d_exprManager, d_lang,
                                              goodBooleanExprs[i], "test");
        TS_ASSERT( !input->done() );
        setupContext(input->getParserState());
        TS_ASSERT( !input->done() );
        Expr e = input->parseNextExpression();
        TS_ASSERT( !e.isNull() );
        e = input->parseNextExpression();
        TS_ASSERT( input->done() );
        TS_ASSERT( e.isNull() );
        delete input;
      } catch (Exception& e) {
        cout << "\nGood expr failed:\n" << goodBooleanExprs[i] << endl;
        cout << e;
        throw;
      }
    }
  }

  void tryBadExprs(InputLanguage d_lang, const string badBooleanExprs[], int numExprs) {
    //Debug.on("parser");
    for(int i = 0; i < numExprs; ++i) {
      // cout << "Testing bad expr: '" << badBooleanExprs[i] << "'\n";
//      istringstream stream(context + badBooleanExprs[i]);
      Input* input = Input::newStringInput(d_exprManager, d_lang,
                                           badBooleanExprs[i], "test");

      TS_ASSERT( !input->done() );
      setupContext(input->getParserState());
      TS_ASSERT( !input->done() );
      TS_ASSERT_THROWS
        ( input->parseNextExpression();
          cout << "\nBad expr succeeded: " << badBooleanExprs[i] << endl;,
          ParserException );
      delete input;
    }
    //Debug.off("parser");
  }

public:
  void setUp() {
    d_exprManager = new ExprManager();
  }

  void tearDown() {
    delete d_exprManager;
  }

  void testBs() {
    DeclarationScope declScope;
    declScope.bind("foo", d_exprManager->mkVar("foo",d_exprManager->booleanType()));

  }

  void testGoodCvc4Inputs() {
    tryGoodInputs(LANG_CVC4,goodCvc4Inputs,numGoodCvc4Inputs);
  }

  void testBadCvc4Inputs() {
    tryBadInputs(LANG_CVC4,badCvc4Inputs,numBadCvc4Inputs);
  }

  void testGoodCvc4Exprs() {
    tryGoodExprs(LANG_CVC4,goodCvc4Exprs,numGoodCvc4Exprs);
  }

  void testBadCvc4Exprs() {
    tryBadExprs(LANG_CVC4,badCvc4Exprs,numBadCvc4Exprs);
  }

  void testGoodSmtInputs() {
    tryGoodInputs(LANG_SMTLIB,goodSmtInputs,numGoodSmtInputs);
  }

  void testBadSmtInputs() {
    tryBadInputs(LANG_SMTLIB,badSmtInputs,numBadSmtInputs);
  }

  void testGoodSmtExprs() {
    tryGoodExprs(LANG_SMTLIB,goodSmtExprs,numGoodSmtExprs);
  }

  void testBadSmtExprs() {
    tryBadExprs(LANG_SMTLIB,badSmtExprs,numBadSmtExprs);
  }
};
