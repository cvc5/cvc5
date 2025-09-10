/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Catching cvc5 exceptions via the C++ API.
 *
 * A simple demonstration of catching cvc5 exceptions via the C++ API.
 */

#include <cvc5/cvc5.h>
#include <iostream>

int main()
{
  cvc5::TermManager tm;
  cvc5::Solver solver(tm);

  solver.setOption("produce-models", "true");

  // Setting an invalid option
  try
  {
    solver.setOption("non-existing", "true");
    return 1;
  }
  catch (const std::exception& e)
  {
    std::cout << e.what() << std::endl;
  }

  // Creating a term with an invalid type
  try
  {
    cvc5::Sort integer = tm.getIntegerSort();
    cvc5::Term x = tm.mkVar(integer, "x");
    cvc5::Term invalidTerm = tm.mkTerm(cvc5::Kind::AND, {x, x});
    solver.checkSatAssuming(invalidTerm);
    return 1;
  }
  catch (const std::exception& e)
  {
    std::cout << e.what() << std::endl;
  }

  // Asking for a model after unsat result
  try
  {
    solver.checkSatAssuming(tm.mkBoolean(false));
    solver.getModel({}, {});
    return 1;
  }
  catch (const std::exception& e)
  {
    std::cout << e.what() << std::endl;
  }

  return 0;
}