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
 * A simple demonstration of using the parser via C++ API.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <iostream>

using namespace cvc5;
using namespace cvc5::parser;

int main()
{
  Solver slv;

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
  ss << "(check-sat)" << std::endl;
  parser.setStreamInput("LANG_SMTLIB_V2_6", ss, "MyStream");

  // get the symbol manager of the parser, used when invoking commands below
  SymbolManager* sm = parser.getSymbolManager();

  // parse commands until finished
  std::unique_ptr<Command> cmd;
  while (cmd = parser.nextCommand())
  {
    std::cout << "Executing command " << *cmd.get() << ":" << std::endl;
    // invoke the command on the solver and the symbol manager, print the result to std::cout
    cmd->invoke(&slv, sm, std::cout);
    if (cmd->fail())
    {
      std::cout << "...the command failed" << std::endl;
    }
    else if (cmd->interrupted())
    {
      std::cout << "...the command was interrupted" << std::endl;
    }
    else if (cmd->ok())
    {
      std::cout << "...the command was successful" << std::endl;
    }
  }
  std::cout << "Finished parsing commands" << std::endl;
}
