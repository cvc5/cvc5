/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include <numeric>

using namespace cvc5;

int main()
{
  // Create a solver
  //! [docs-cpp-quickstart-1 start]
  Solver solver;
  //! [docs-cpp-quickstart-1 end]

  // We will ask the solver to produce models and unsat cores,
  // hence these options should be turned on.
  //! [docs-cpp-quickstart-2 start]
  solver.setOption("produce-models", "true");
  solver.setOption("produce-unsat-cores", "true");
  //! [docs-cpp-quickstart-2 end]

  // The simplest way to set a logic for the solver is to choose "ALL".
  // This enables all logics in the solver.
  // Alternatively, "QF_ALL" enables all logics without quantifiers.
  // To optimize the solver's behavior for a more specific logic,
  // use the logic name, e.g. "QF_BV" or "QF_AUFBV".

  // Set the logic
  //! [docs-cpp-quickstart-3 start]
  solver.setLogic("ALL");
  //! [docs-cpp-quickstart-3 end]

  // In this example, we will define constraints over reals and integers.
  // Hence, we first obtain the corresponding sorts.
  //! [docs-cpp-quickstart-4 start]
  Sort realSort = solver.getRealSort();
  Sort intSort = solver.getIntegerSort();
  //! [docs-cpp-quickstart-4 end]

  // x and y will be real variables, while a and b will be integer variables.
  // Formally, their cpp type is Term,
  // and they are called "constants" in SMT jargon:
  //! [docs-cpp-quickstart-5 start]
  Term x = solver.mkConst(realSort, "x");
  Term y = solver.mkConst(realSort, "y");
  Term a = solver.mkConst(intSort, "a");
  Term b = solver.mkConst(intSort, "b");
  //! [docs-cpp-quickstart-5 end]

  // Our constraints regarding x and y will be:
  //
  //   (1)  0 < x
  //   (2)  0 < y
  //   (3)  x + y < 1
  //   (4)  x <= y
  //

  //! [docs-cpp-quickstart-6 start]
  // Formally, constraints are also terms. Their sort is Boolean.
  // We will construct these constraints gradually,
  // by defining each of their components.
  // We start with the constant numerals 0 and 1:
  Term zero = solver.mkReal(0);
  Term one = solver.mkReal(1);

  // Next, we construct the term x + y
  Term xPlusY = solver.mkTerm(ADD, {x, y});

  // Now we can define the constraints.
  // They use the operators +, <=, and <.
  // In the API, these are denoted by ADD, LEQ, and LT.
  // A list of available operators is available in:
  // src/api/cpp/cvc5_kind.h
  Term constraint1 = solver.mkTerm(LT, {zero, x});
  Term constraint2 = solver.mkTerm(LT, {zero, y});
  Term constraint3 = solver.mkTerm(LT, {xPlusY, one});
  Term constraint4 = solver.mkTerm(LEQ, {x, y});

  // Now we assert the constraints to the solver.
  solver.assertFormula(constraint1);
  solver.assertFormula(constraint2);
  solver.assertFormula(constraint3);
  solver.assertFormula(constraint4);
  //! [docs-cpp-quickstart-6 end]

  // Check if the formula is satisfiable, that is,
  // are there real values for x and y that satisfy all the constraints?
  //! [docs-cpp-quickstart-7 start]
  Result r1 = solver.checkSat();
  //! [docs-cpp-quickstart-7 end]

  // The result is either SAT, UNSAT, or UNKNOWN.
  // In this case, it is SAT.
  //! [docs-cpp-quickstart-8 start]
  std::cout << "expected: sat" << std::endl;
  std::cout << "result: " << r1 << std::endl;
  //! [docs-cpp-quickstart-8 end]

  // We can get the values for x and y that satisfy the constraints.
  //! [docs-cpp-quickstart-9 start]
  Term xVal = solver.getValue(x);
  Term yVal = solver.getValue(y);
  //! [docs-cpp-quickstart-9 end]

  // It is also possible to get values for compound terms,
  // even if those did not appear in the original formula.
  //! [docs-cpp-quickstart-10 start]
  Term xMinusY = solver.mkTerm(SUB, {x, y});
  Term xMinusYVal = solver.getValue(xMinusY);
  //! [docs-cpp-quickstart-10 end]

  // We can now obtain the string representations of the values.
  //! [docs-cpp-quickstart-11 start]
  std::string xStr = xVal.getRealValue();
  std::string yStr = yVal.getRealValue();
  std::string xMinusYStr = xMinusYVal.getRealValue();

  std::cout << "value for x: " << xStr << std::endl;
  std::cout << "value for y: " << yStr << std::endl;
  std::cout << "value for x - y: " << xMinusYStr << std::endl;
  //! [docs-cpp-quickstart-11 end]

  //! [docs-cpp-quickstart-12 start]
  // Further, we can convert the values to cpp types
  std::pair<int64_t, uint64_t> xPair = xVal.getReal64Value();
  std::pair<int64_t, uint64_t> yPair = yVal.getReal64Value();
  std::pair<int64_t, uint64_t> xMinusYPair = xMinusYVal.getReal64Value();

  std::cout << "value for x: " << xPair.first << "/" << xPair.second
            << std::endl;
  std::cout << "value for y: " << yPair.first << "/" << yPair.second
            << std::endl;
  std::cout << "value for x - y: " << xMinusYPair.first << "/"
            << xMinusYPair.second << std::endl;
  //! [docs-cpp-quickstart-12 end]

  // Another way to independently compute the value of x - y would be
  // to perform the (rational) arithmetic manually.
  // However, for more complex terms,
  // it is easier to let the solver do the evaluation.
  //! [docs-cpp-quickstart-13 start]
  std::pair<int64_t, uint64_t> xMinusYComputed = {
    xPair.first * yPair.second - xPair.second * yPair.first,
    xPair.second * yPair.second
  };
  uint64_t g = std::gcd(xMinusYComputed.first, xMinusYComputed.second);
  xMinusYComputed = { xMinusYComputed.first / g, xMinusYComputed.second / g };
  if (xMinusYComputed == xMinusYPair)
  {
    std::cout << "computed correctly" << std::endl;
  }
  else
  {
    std::cout << "computed incorrectly" << std::endl;
  }
  //! [docs-cpp-quickstart-13 end]

  // Next, we will check satisfiability of the same formula,
  // only this time over integer variables a and b.

  // We start by resetting assertions added to the solver.
  //! [docs-cpp-quickstart-14 start]
  solver.resetAssertions();
  //! [docs-cpp-quickstart-14 end]

  // Next, we assert the same assertions above with integers.
  // This time, we inline the construction of terms
  // to the assertion command.
  //! [docs-cpp-quickstart-15 start]
  solver.assertFormula(solver.mkTerm(LT, {solver.mkInteger(0), a}));
  solver.assertFormula(solver.mkTerm(LT, {solver.mkInteger(0), b}));
  solver.assertFormula(
      solver.mkTerm(LT, {solver.mkTerm(ADD, {a, b}), solver.mkInteger(1)}));
  solver.assertFormula(solver.mkTerm(LEQ, {a, b}));
  //! [docs-cpp-quickstart-15 end]

  // We check whether the revised assertion is satisfiable.
  //! [docs-cpp-quickstart-16 start]
  Result r2 = solver.checkSat();
  //! [docs-cpp-quickstart-16 end]

  // This time the formula is unsatisfiable
  //! [docs-cpp-quickstart-17 start]
  std::cout << "expected: unsat" << std::endl;
  std::cout << "result: " << r2 << std::endl;
  //! [docs-cpp-quickstart-17 end]

  // We can query the solver for an unsatisfiable core, i.e., a subset
  // of the assertions that is already unsatisfiable.
  //! [docs-cpp-quickstart-18 start]
  std::vector<Term> unsatCore = solver.getUnsatCore();
  std::cout << "unsat core size: " << unsatCore.size() << std::endl;
  std::cout << "unsat core: " << std::endl;
  for (const Term& t : unsatCore)
  {
    std::cout << t << std::endl;
  }
  //! [docs-cpp-quickstart-18 end]

  return 0;
}
