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
  
  // In this example we will ask the solver to produce
  // models and unsat cores, hence these options
  // should be turned on.
  solver.setOption("produce-models", "true");
  solver.setOption("produce-unsat-cores", "true");

  // The simplest way to set a logic for the solver is to choose "ALL".
  // This enables all logics in the solver.
  // To optimize the solver's behavior for a more specific logic,
  // use the logic name, e.g. "QF_BV" or "QF_AUFBV".
  solver.setLogic("ALL");  // Set the logic

  // In this example, we will define constraints
  // over reals and integers.
  // Hence we first obtain the corresponding sorts.
  Sort realSort = solver.getRealSort();
  Sort intSort = solver.getIntegerSort();

  // x,y will be real variables, while
  // a,b will be integer variables.
  // Formally, their cpp type is Term, and 
  // they are called "constants" in SMT jargon,
  Term x = solver.mkConst(realSort, "x");
  Term y = solver.mkConst(realSort, "y");
  Term a = solver.mkConst(intSort, "a");
  Term b = solver.mkConst(intSort, "b");
  
  // Our constraints regarding x,y,z will be:
  // '''
  //    0 < x
  //    0 < y
  //    x+y < 1
  //    x<=y 
  // '''

  // Formally, constraints are also terms. Their sort is Boolean.
  // We will construct these constraints gradually,
  // by defining each of their components.
  // We start with the constant numerals 0 and 2:
  Term zero = solver.mkReal(0);
  Term one = solver.mkReal(1);

  // Next, we continue with the compound terms, that 
  // employ +, <=, and <.
  // In the API, these are denoted by
  // PLUS, LEQ, and LT.
  // A list of operators is available in... 
  // src/api/cpp/cvc5_kind.h
  Term xPlusY = solver.mkTerm(PLUS, x, y);
  // Now we can define the first and second constraints:
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
  // are there real x,y,z that satisfy all three
  // constraints.
  Result r1 = solver.checkSat();

  // The result is either SAT, UNSAT, or UNKNOWN.
  // In this case, it is SAT.
  std::cout << "result:" << r1 << std::endl;

  // We can get actual values for x,y,z that 
  // satisfy the constraints.
  Term xVal = solver.getValue(x);
  Term yVal = solver.getValue(y);

  // To cast these values to cpp types,
  // we first obtain their string representations
  // from the solver.
  std::string xStr = xVal.getRealValue();
  std::string yStr = yVal.getRealValue();

  // now we can convert the values to cpp types
  // using standard cpp conversion functions.
  double xDouble = std::stod(xStr);
  double yDouble = std::stod(yStr);
  
  std::cout << "solution for x: " << xDouble << std::endl;
  std::cout << "solution for y: " << yDouble << std::endl;

  // Next, we will check satisfiability of the same formula,
  // only this time over integer variables a,b,c
  
  // We start by reseting the solver to flush
  // previous assertions.
  solver.resetAssertions();

  // Next, we assert the same assertions above with integers,
  // in an abbreviated manner.
  // Notice that a different division operator is used,
  // namely INTS_DIVISION.
  solver.assertFormula(solver.mkTerm(LT, solver.mkInteger(0), a));
  solver.assertFormula(solver.mkTerm(LT, solver.mkInteger(0), b));
  solver.assertFormula(
        solver.mkTerm(LT, solver.mkTerm(PLUS, a, b), solver.mkInteger(1)));
  solver.assertFormula(
        solver.mkTerm(LEQ, a, b)
      );
  // We check whether the revised assertion is satisfiable.
  Result r2 = solver.checkSat();

  // This time the formula is unsatisfiable
  std::cout << "result: " << r2 << std::endl;

  // Obviously, we cannot get values for a,b,c, as
  // no values exist that make the formula true.
  // However, we can query the solver
  // for an unsatisfiable core, i.e., a subset
  // of the assertions that is already unsatisfiable.
  std::vector<Term> unsatCore = solver.getUnsatCore();
  std::cout << "unsat core size: " << unsatCore.size() << std::endl;
  std::cout << "unsat core: " << std::endl;
  for (const Term & t : unsatCore) {
    std::cout << t << std::endl;
  }

  return 0;
}
