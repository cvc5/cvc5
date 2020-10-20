/*********************                                                        */
/*! \file smt2_compliance.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A test of SMT-LIBv2 commands, checks for compliant output
 **
 ** A test of SMT-LIBv2 commands, checks for compliant output.
 **/

#include <cassert>
#include <iostream>
#include <sstream>

#include "api/cvc4cpp.h"
#include "expr/expr_manager.h"
#include "options/options.h"
#include "options/set_language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace CVC4::parser;
using namespace std;

void testGetInfo(api::Solver* solver, const char* s);

int main()
{
  Options opts;
  opts.setInputLanguage(language::input::LANG_SMTLIB_V2);
  opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);

  cout << language::SetLanguage(language::output::LANG_SMTLIB_V2);

  std::unique_ptr<api::Solver> solver =
      std::unique_ptr<api::Solver>(new api::Solver(&opts));

  testGetInfo(solver.get(), ":error-behavior");
  testGetInfo(solver.get(), ":name");
  testGetInfo(solver.get(), ":authors");
  testGetInfo(solver.get(), ":version");
  testGetInfo(solver.get(), ":status");
  testGetInfo(solver.get(), ":reason-unknown");
  testGetInfo(solver.get(), ":arbitrary-undefined-keyword");
  testGetInfo(solver.get(), ":56");  // legal
  testGetInfo(solver.get(), ":<=");  // legal
  testGetInfo(solver.get(), ":->");  // legal
  testGetInfo(solver.get(), ":all-statistics");

  return 0;
}

void testGetInfo(api::Solver* solver, const char* s)
{
  ParserBuilder pb(solver, "<internal>", solver->getOptions());
  Parser* p = pb.withStringInput(string("(get-info ") + s + ")").build();
  assert(p != NULL);
  Command* c = p->nextCommand();
  assert(c != NULL);
  cout << c << endl;
  stringstream ss;
  c->invoke(solver, ss);
  assert(p->nextCommand() == NULL);
  delete p;
  delete c;
  cout << ss.str() << endl << endl;
}
