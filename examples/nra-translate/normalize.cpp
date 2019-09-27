/*********************                                                        */
/*! \file normalize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Aina Niemetz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <cassert>
#include <iostream>
#include <map>
#include <string>
#include <typeinfo>
#include <vector>

#include <cvc4/api/cvc4cpp.h>
#include <cvc4/cvc4.h>
#include <cvc4/expr/expr_iomanip.h>
#include <cvc4/options/set_language.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::theory;

int main(int argc, char* argv[])
{

  // Get the filename
  string input(argv[1]);

  // Create the expression manager
  Options options;
  options.setInputLanguage(language::input::LANG_SMTLIB_V2);
  std::unique_ptr<api::Solver> solver =
      std::unique_ptr<api::Solver>(new api::Solver(&options));

  cout << language::SetLanguage(language::output::LANG_SMTLIB_V2)
       << expr::ExprSetDepth(-1);

  // Create the parser
  ParserBuilder parserBuilder(solver.get(), input, options);
  Parser* parser = parserBuilder.build();

  // Variables and assertions
  vector<Expr> assertions;

  Command* cmd;
  while ((cmd = parser->nextCommand())) {

    AssertCommand* assert = dynamic_cast<AssertCommand*>(cmd);
    if (assert) {
      Expr normalized = solver->getSmtEngine()->simplify(assert->getExpr());
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
