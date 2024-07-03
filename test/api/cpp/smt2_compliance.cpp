/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A test of SMT-LIBv2 commands, checks for compliant output.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <cassert>
#include <iostream>
#include <sstream>

using namespace cvc5;
using namespace cvc5::internal;
using namespace cvc5::parser;
using namespace std;

void testGetInfo(cvc5::Solver* solver, const char* s);

int main()
{
  cvc5::TermManager tm;
  std::unique_ptr<cvc5::Solver> solver = std::make_unique<cvc5::Solver>(tm);
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
  std::unique_ptr<SymbolManager> symman(
      new SymbolManager(solver->getTermManager()));

  InputParser p(solver, symman.get());
  std::stringstream ssi;
  ssi << "(get-info " << s << ")";
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ssi, "<internal>");
  Command c = p.nextCommand();
  assert(!c.isNull());
  std::cout << c << std::endl;
  std::stringstream ss;
  c.invoke(solver, symman.get(), ss);
  c = p.nextCommand();
  assert(c.isNull());
  std::cout << ss.str() << std::endl << std::endl;
}
