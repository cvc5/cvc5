/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #11069.
 */
#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <cassert>
#include <iostream>

using namespace cvc5;
using namespace cvc5::parser;

int main()
{
  TermManager tm;
  Solver slv(tm);

  SymbolManager sm(tm);

  slv.setLogic("QF_BV");

  // construct an input parser associated the solver above
  InputParser parser(&slv, &sm);

  std::string input1("(declare-const x (_ BitVec 4))\n(assert (= x #b0001))\n");

  parser.setIncrementalStringInput(modes::InputLanguage::SMT_LIB_2_6,
                                   "myInput");
  parser.appendIncrementalStringInput(input1);

  // parse commands until finished
  Command cmd;
  while (true)
  {
    cmd = parser.nextCommand();
    if (cmd.isNull())
    {
      break;
    }
    cmd.invoke(&slv, &sm, std::cout);
  }
  Result result = slv.checkSat();
  std::cout << "Result:" << result << std::endl;

  std::string input2("(assert (= x #b0101))");
  parser.appendIncrementalStringInput(input2);
  cmd = parser.nextCommand();
  assert(!cmd.isNull());
  cmd.invoke(&slv, &sm, std::cout);
  result = slv.checkSat();
  std::cout << "Result:" << result << std::endl;
  assert(result.isUnsat());
  return 0;
}
