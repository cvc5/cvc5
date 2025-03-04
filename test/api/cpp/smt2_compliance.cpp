/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

void testGetInfo(cvc5::Solver& solver, const char* s)
{
  SymbolManager sm(solver.getTermManager());
  InputParser p(&solver, &sm);
  std::stringstream ssi;
  ssi << "(get-info " << s << ")";
  p.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ssi, "<internal>");
  Command c = p.nextCommand();
  assert(!c.isNull());
  std::cout << c << std::endl;
  std::stringstream ss;
  c.invoke(&solver, &sm, ss);
  c = p.nextCommand();
  assert(c.isNull());
  std::cout << ss.str();
}

int main()
{
  cvc5::TermManager tm;
  cvc5::Solver solver(tm);
  solver.setOption("input-language", "smtlib2");
  solver.setOption("output-language", "smtlib2");
  testGetInfo(solver, ":error-behavior");
  testGetInfo(solver, ":name");
  testGetInfo(solver, ":authors");
  testGetInfo(solver, ":version");
  testGetInfo(solver, ":status");
  testGetInfo(solver, ":reason-unknown");
  testGetInfo(solver, ":arbitrary-undefined-keyword");
  testGetInfo(solver, ":<=");  // legal
  testGetInfo(solver, ":->");  // legal
  testGetInfo(solver, ":all-statistics");

  return 0;
}
