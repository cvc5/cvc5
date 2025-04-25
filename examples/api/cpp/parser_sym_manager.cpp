/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of using multiple parsers with the same symbol manager
 * via C++ API.
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

  SymbolManager sm(tm);

  // construct an input parser associated the solver above
  InputParser parser(&slv, &sm);

  std::stringstream ss;
  ss << "(set-logic QF_LIA)" << std::endl;
  ss << "(declare-fun a () Int)" << std::endl;
  ss << "(declare-fun b () Int)" << std::endl;
  ss << "(declare-fun c () Bool)" << std::endl;
  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "MyStream");

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
    cmd.invoke(&slv, &sm, std::cout);
  }
  std::cout << "Finished parsing commands" << std::endl;

  // Note that sm now has a,b,c in its symbol table.

  // Now, construct a new parser with the same symbol manager. We will parse
  // terms with it.
  InputParser parser2(&slv, &sm);
  std::stringstream ss2;
  ss2 << "(+ a b)" << std::endl;
  ss2 << "(- a 10)" << std::endl;
  ss2 << "(>= 0 45)" << std::endl;
  ss2 << "(and c c)" << std::endl;
  ss2 << "true" << std::endl;
  parser2.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss2, "MyStream2");

  // parse terms until finished
  Term t;
  do
  {
    t = parser2.nextTerm();
    std::cout << "Parsed term: " << t << std::endl;
  } while (!t.isNull());
  std::cout << "Finished parsing terms" << std::endl;
}
