/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of using multiple parsers with the same symbol manager via C++ API.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <iostream>

using namespace cvc5;
using namespace cvc5::parser;

int main()
{
  Solver slv;

  SymbolManager sm(&slv);

  // construct an input parser associated the solver above
  InputParser parser(&slv, &sm);

  std::stringstream ss;
  ss << "(set-logic QF_LIA)" << std::endl;
  ss << "(declare-fun a () Int)" << std::endl;
  ss << "(declare-fun b () Int)" << std::endl;
  ss << "(declare-fun c () Int)" << std::endl;
  parser.setStreamInput("LANG_SMTLIB_V2_6", ss, "MyStream");

  // parse commands until finished
  std::unique_ptr<Command> cmd;
  while (cmd = d_parser->nextCommand())
  {
    std::cout << "Executing command " << *cmd.get() << ":" << std::endl;
    // invoke the command on the solver and the symbol manager, print the result to std::cout
    cmd->invoke(&slv, &sm, std::cout);
  }
  std::cout << "Finished parsing commands" << std::endl;

  // Note that sm now has a,b,c in its symbol table.

  // Now, construct a new parser with the same symbol manager
  InputParser parser2(&slv, &sm);
  std::stringstream ss2;
  ss2 << "(+ a b)" << std::endl;
  ss2 << "(+ c 10)" << std::endl;
  ss2 << "(>= 0 45)" << std::endl;

  // parse terms until finished
  Term t;
  do
  {
    t = d_parser->nextTerm();
    std::cout << "Parsed term: " << t << std::endl;
  }while (!t.isNull());
  std::cout << "Finished parsing terms" << std::endl;
}
