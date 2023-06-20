/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A test of SMT-LIBv2 commands, checks for compliant output.
 */

#include <cvc5/cvc5.h>

#include <cassert>
#include <iostream>
#include <sstream>

#include "parser/api/cpp/command.h"
#include "parser/api/cpp/input_parser.h"

using namespace cvc5;
using namespace cvc5::internal;
using namespace cvc5::parser;
using namespace std;

void testGetInfo(cvc5::Solver* solver, const char* s);

int main()
{
  std::unique_ptr<cvc5::Solver> solver = std::make_unique<cvc5::Solver>();
  solver->setOption("input-language", "smtlib2");
  solver->setOption("output-language", "smtlib2");
  testGetInfo(solver.get(), ":error-behavior");
  testGetInfo(solver.get(), ":name");
  testGetInfo(solver.get(), ":authors");
  testGetInfo(solver.get(), ":version");
  testGetInfo(solver.get(), ":status");
  testGetInfo(solver.get(), ":reason-unknown");
  testGetInfo(solver.get(), ":arbitrary-undefined-keyword");
  testGetInfo(solver.get(), ":<=");  // legal
  testGetInfo(solver.get(), ":->");  // legal
  testGetInfo(solver.get(), ":all-statistics");

  return 0;
}

void testGetInfo(cvc5::Solver* solver, const char* s)
{
  std::unique_ptr<SymbolManager> symman(new SymbolManager(solver));

  InputParser p(solver, symman.get());
  std::stringstream ssi;
  ssi << "(get-info " << s << ")";
  p.setStreamInput("LANG_SMTLIB_V2_6", ssi, "<internal>");
  std::unique_ptr<Command> c = p.nextCommand();
  assert(c != nullptr);
  std::cout << c.get() << std::endl;
  std::stringstream ss;
  c->invoke(solver, symman.get(), ss);
  assert(p.nextCommand() == nullptr);
  std::cout << ss.str() << std::endl << std::endl;
}
