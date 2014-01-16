/*********************                                                        */
/*! \file normalize.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <string>
#include <iostream>
#include <typeinfo>
#include <cassert>
#include <vector>
#include <map>


#include "options/options.h"
#include "expr/expr.h"
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/smt_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::options;
using namespace CVC4::theory;

int main(int argc, char* argv[]) 
{

  // Get the filename 
  string input(argv[1]);

  // Create the expression manager
  Options options;
  options.set(inputLanguage, language::input::LANG_SMTLIB_V2);
  ExprManager exprManager(options);
  
  cout << Expr::setlanguage(language::output::LANG_SMTLIB_V2) << Expr::setdepth(-1);

  // Create the parser
  ParserBuilder parserBuilder(&exprManager, input, options);
  Parser* parser = parserBuilder.build();

  // Smt manager for simplifications
  SmtEngine engine(&exprManager);

  // Variables and assertions
  vector<Expr> assertions;

  Command* cmd;
  while ((cmd = parser->nextCommand())) {

    AssertCommand* assert = dynamic_cast<AssertCommand*>(cmd);
    if (assert) {
      Expr normalized = engine.simplify(assert->getExpr());
      cout << "(assert " << normalized << ")" << endl;
      delete cmd;
      continue;
    }

    CheckSatCommand* checksat = dynamic_cast<CheckSatCommand*>(cmd);
    if (checksat) {
      delete cmd;
      continue;
    }

    cout << *cmd << endl;
    delete cmd;  
  }

  cout << "(check-sat)" << endl;
	
  // Get rid of the parser
  delete parser;
}

