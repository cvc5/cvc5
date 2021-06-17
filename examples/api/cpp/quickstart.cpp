/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the api capabilities of cvc5.
 *
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5::api;

int main()
{
  // Create a solver
  Solver solver;

  // We will ask the solver to produce models and unsat cores,
  // hence these options should be turned on.
  solver.setOption("produce-models", "true");
  solver.setOption("produce-unsat-cores", "true");

  // The simplest way to set a logic for the solver is to choose "ALL".
  // This enables all logics in the solver.
  // Alternatively, "QF_ALL" enables all logics without quantifiers.
  // To optimize the solver's behavior for a more specific logic,
  // use the logic name, e.g. "QF_BV" or "QF_AUFBV".

  // Set the logic
  solver.setLogic("ALL");

  // In this example, we will define constraints over reals and integers.
  // Hence, we first obtain the corresponding sorts.
  Sort realSort = solver.getRealSort();
  Sort intSort = solver.getIntegerSort();

  // x and y will be real variables, while a and b will be integer variables.
  // Formally, their cpp type is Term,
  // and they are called "constants" in SMT jargon:
  Term x = solver.mkConst(realSort, "x");
  Term y = solver.mkConst(realSort, "y");
  Term a = solver.mkConst(intSort, "a");
  Term b = solver.mkConst(intSort, "b");

  // Our constraints regarding x and y will be:
  //
  //   (1)  0 < x
  //   (2)  0 < y
  //   (3)  x + y < 1
  //   (4)  x <= y
  //

  // Formally, constraints are also terms. Their sort is Boolean.
  // We will construct these constraints gradually,
  // by defining each of their components.
  // We start with the constant numerals 0 and 1:
  Term zero = solver.mkReal(0);
  Term one = solver.mkReal(1);

  // Next, we construct the term x + y
  Term xPlusY = solver.mkTerm(PLUS, x, y);

  // Now we can define the constraints.
  // They use the operators +, <=, and <.
  // In the API, these are denoted by PLUS, LEQ, and LT.
  // A list of available operators is available in:
  // src/api/cpp/cvc5_kind.h
  Term constraint1 = solver.mkTerm(LT, zero, x);
  Term constraint2 = solver.mkTerm(LT, zero, y);
  Term constraint3 = solver.mkTerm(LT, xPlusY, one);
  Term constraint4 = solver.mkTerm(LEQ, x, y);

  // Now we assert the constraints to the solver.
  solver.assertFormula(constraint1);
  solver.assertFormula(constraint2);
  solver.assertFormula(constraint3);
  solver.assertFormula(constraint4);

  // Check if the formula is satisfiable, that is,
  // are there real values for x,y,z that satisfy all the constraints?
  Result r1 = solver.checkSat();

  // The result is either SAT, UNSAT, or UNKNOWN.
  // In this case, it is SAT.
  std::cout << "expected: sat" << std::endl;
  std::cout << "result:" << r1 << std::endl;

  // We can get the values for x and y that satisfy the constraints.
  Term xVal = solver.getValue(x);
  Term yVal = solver.getValue(y);

  // It is also possible to get values for compound terms,
  // even if those did not appear in the original formula.
  Term xMinusY = solver.mkTerm(MINUS, x, y);
  Term xMinusYVal = solver.getValue(xMinusY);

  // We can now obtain thestring representations of the values.
  std::string xStr = xVal.getRealValue();
  std::string yStr = yVal.getRealValue();
  std::string xMinusYStr = xMinusYVal.getRealValue();

  std::cout << "value for x: " << xStr << std::endl;
  std::cout << "value for y: " << yStr << std::endl;
  std::cout << "value for x - y: " << xMinusYStr << std::endl;

  // Further, we can convert the values to cpp types,
  // using standard cpp conversion functions.
  double xDouble = std::stod(xStr);
  double yDouble = std::stod(yStr);
  double xMinusYDouble = std::stod(xMinusYStr);

  // Another way to independently compute the value of x and y would be using
  // the ordinary cpp minus operator instead of asking the solver.
  // However, for more complex terms,
  // it is easier to let the solver do the evaluation.
  double xMinusYComputed = xDouble - yDouble;
  if (xMinusYComputed == xMinusYDouble)
  {
    std::cout << "computed correctly" << std::endl;
  }
  else
  {
    std::cout << "computed incorrectly" << std::endl;
  }

  // Next, we will check satisfiability of the same formula,
  // only this time over integer variables a and b.

  // We start by resetting assertions added to the solver.
  solver.resetAssertions();

  // Next, we assert the same assertions above with integers.
  // This time, we inline the construction of terms
  // to the assertion command.
  solver.assertFormula(solver.mkTerm(LT, solver.mkInteger(0), a));
  solver.assertFormula(solver.mkTerm(LT, solver.mkInteger(0), b));
  solver.assertFormula(
      solver.mkTerm(LT, solver.mkTerm(PLUS, a, b), solver.mkInteger(1)));
  solver.assertFormula(solver.mkTerm(LEQ, a, b));

  // We check whether the revised assertion is satisfiable.
  Result r2 = solver.checkSat();

  // This time the formula is unsatisfiable
  std::cout << "expected: unsat" << std::endl;
  std::cout << "result: " << r2 << std::endl;

  // We can query the solver for an unsatisfiable core, i.e., a subset
  // of the assertions that is already unsatisfiable.
  std::vector<Term> unsatCore = solver.getUnsatCore();
  std::cout << "unsat core size: " << unsatCore.size() << std::endl;
  std::cout << "unsat core: " << std::endl;
  for (const Term& t : unsatCore)
  {
    std::cout << t << std::endl;
  }

  return 0;
}
