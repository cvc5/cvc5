/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of using the parser via C++ API.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <iostream>

using namespace cvc5;
using namespace cvc5::parser;

int main()
{
  TermManager tm;
  Solver slv(tm);

  // set that we should print success after each successful command
  slv.setOption("print-success", "true");

  // construct an input parser associated the solver above
  InputParser parser(&slv);

  std::stringstream ss;
  ss << "(set-logic QF_LIA)" << std::endl;
  ss << "(declare-fun a () Int)" << std::endl;
  ss << "(declare-fun b () Int)" << std::endl;
  ss << "(declare-fun c () Int)" << std::endl;
  ss << "(assert (> a (+ b c)))" << std::endl;
  ss << "(assert (< a b))" << std::endl;
  ss << "(assert (> c 0))" << std::endl;
  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "MyStream");

  // get the symbol manager of the parser, used when invoking commands below
  SymbolManager* sm = parser.getSymbolManager();

  // parse commands until finished
  Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    std::cout << "Executing command " << cmd << ":" << std::endl;
    // invoke the command on the solver and the symbol manager, print the result
    // to std::cout
    cmd.invoke(&slv, sm, std::cout);
  }
  std::cout << "Finished parsing commands" << std::endl;

  // now, check sat with the solver
  Result r = slv.checkSat();
  std::cout << "expected: unsat" << std::endl;
  std::cout << "result: " << r << std::endl;
}
