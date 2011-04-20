/*********************                                                        */
/*! \file ouroborous.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief "Ouroborous" test: does CVC4 read its own output?
 **
 ** The "Ouroborous" test, named after the serpent that swallows its own
 ** tail, ensures that CVC4 can parse some input, output it again (in any
 ** of its languages) and then parse it again.  The result of the first
 ** parse must be equal to the result of the second parse (up to renaming
 ** variables), or the test fails.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "expr/expr.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::language;
using namespace std;

const string declarations = "\
(declare-sort U 0)\n\
(declare-fun f (U) U)\n\
(declare-fun x () U)\n\
(declare-fun y () U)\n\
(assert (= (f x) x))\n\
";

int runTest();

int main() {
  try {
    return runTest();
  } catch(Exception& e) {
    cerr << e << endl;
  } catch(...) {
    cerr << "non-cvc4 exception thrown." << endl;
  }
  return 1;
}

string translate(Parser* parser, string in, InputLanguage inlang, OutputLanguage outlang) {
  cout << "==============================================" << endl
       << "translating from " << inlang << " to " << outlang << " this string:" << endl
       << in << endl;
  parser->setInput(Input::newStringInput(inlang, in, "internal-buffer"));
  stringstream ss;
  ss << Expr::setlanguage(outlang) << parser->nextExpression();
  AlwaysAssert(parser->nextExpression().isNull(), "next expr should be null");
  AlwaysAssert(parser->done(), "parser should be done");
  string s = ss.str();
  cout << "got this:" << endl
       << s << endl
       << "==============================================" << endl;
  return s;
}

int runTest() {
  ExprManager em;
  Parser* parser =
    ParserBuilder(&em, "internal-buffer")
      .withStringInput(declarations)
      .withInputLanguage(input::LANG_SMTLIB_V2)
      .build();

  // we don't need to execute them, but we DO need to parse them to
  // get the declarations
  while(Command* c = parser->nextCommand()) {
    delete c;
  }

  AlwaysAssert(parser->done(), "parser should be done");

  string instr = "(= (f (f y)) x)";
  cout << "starting with: " << instr << endl;
  string smt2 = translate(parser, instr, input::LANG_SMTLIB_V2, output::LANG_SMTLIB_V2);
  cout << "in SMT2      : " << smt2 << endl;
  string smt1 = translate(parser, smt2, input::LANG_SMTLIB_V2, output::LANG_SMTLIB);
  cout << "in SMT1      : " << smt1 << endl;
  string cvc = translate(parser, smt1, input::LANG_SMTLIB, output::LANG_CVC4);
  cout << "in CVC       : " << cvc << endl;
  string out = translate(parser, cvc, input::LANG_CVC4, output::LANG_SMTLIB_V2);
  cout << "back to SMT2 : " << out << endl;

  AlwaysAssert(out == smt2, "differences in output");

  delete parser;

  return 0;
}

