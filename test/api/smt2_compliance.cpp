/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A test of SMT-LIBv2 commands, checks for compliant output.
 */

#include <cassert>
#include <iostream>
#include <sstream>

#include "api/cpp/cvc5.h"
#include "options/options.h"
#include "options/set_language.h"
#include "parser/parser.h"
#include "parser/parser_builder.h"
#include "smt/command.h"
#include "smt/smt_engine.h"

using namespace cvc5;
using namespace cvc5::parser;
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
  std::unique_ptr<SymbolManager> symman(new SymbolManager(solver));

  std::unique_ptr<Parser> p(
      ParserBuilder(solver, symman.get(), solver->getOptions()).build());
  p->setInput(Input::newStringInput(language::input::LANG_SMTLIB_V2,
                                    string("(get-info ") + s + ")",
                                    "<internal>"));
  assert(p != NULL);
  Command* c = p->nextCommand();
  assert(c != NULL);
  cout << c << endl;
  stringstream ss;
  c->invoke(solver, symman.get(), ss);
  assert(p->nextCommand() == NULL);
  delete c;
  cout << ss.str() << endl << endl;
}
