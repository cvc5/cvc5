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

  // x,y,z will be real variables, while
  // a,b,c will be integer variables.
  // Formally, their cpp type is Term, and 
  // they are called "constants" in SMT jargon,
  Term x = solver.mkConst(realSort, "x");
  Term y = solver.mkConst(realSort, "y");
  Term z = solver.mkConst(realSort, "z");
  Term a = solver.mkConst(intSort, "a");
  Term b = solver.mkConst(intSort, "");
  Term c = solver.mkConst(intSort, "a");
  
  // Our constraints regarding x,y,z will be:
  // '''
  //    0 <= (x+y)/2
  //    z < 2
  //    x+y < 2*z
  // '''
  // Formally, constraints are also terms. Their sort is Boolean.
  // We will construct these constraints gradually,
  // by defining each of their components.
  // We start with the constant numerals 0 and 2:
  Term zero = solver.mkReal(0);
  Term two = solver.mkReal(2);

  // Next, we continue with the compound terms, that 
  // employ +, <=, < and *.
  // In the API, these are denoted by
  // PLUS, LEQ, LT, and MULT, respectively.
  // A list of operators is available in... 
  // TODO where?
  Term xPlusY = solver.mkTerm(PLUS, x, y);
  // We continue with the remaining sub-terms:
  Term xPlusYDivTwo = solver.mkTerm(DIV, xPlusY, two);
  // Now we can define the first and second constraints:
  Term constraint1 = solver.mkTerm(LEQ, zero, xPlusYDivTwo);
  Term constraint2 = solver.mkTerm(LT, z, two);

  // For the third constraint, we need 2*z:
  Term twoZ = solver.mkTerm(MULT, twom z);
  Term constraint3 = solver.mkTerm(LT, xPluxY, twoZ);

  // Now we assert the constraints to the solver.
  solver.assertFormula(constraint1);
  solver.assertFormula(constraint2);
  solver.assertFormula(constraint3);

  // Check if the formula is satisfiable, that is,
  // are there real x,y,z that satisfy all three
  // constraints.
  Result r = solver.checkSat();

  // The result is either SAT, UNSAT, or UNKNOWN.
  // In this case, it is SAT.
  std::cout << r << std::endl;

  // We can get actual values for x,y,z that 
  // satisfy the constraints.
  Term xVal = solver.getValue(x);
  Term yVal = solver.getValue(y);
  Term zVal = solver.getValue(z);

  // To cast these values to cpp types,
  // we first obtain their string representations
  // from the solver.
  std::string xStr = xVal.getRealValue();
  std::string yStr = yVal.getRealValue();
  std::string zStr = zVal.getRealValue();

  // now we can convert the values to cpp types
  // using standard cpp conversion functions.
  double xDouble = std::stod(xStr);
  double yDouble = std::stod(yStr);
  double zDouble = std::stod(zStr);
  
  std::cout << "solution for x: " << xDouble << std::endl;
  std::cout << "solution for y: " << yDouble << std::endl;
  std::cout << "solution for z: " << zDouble << std::endl;

  // Next, we will check satisfiability of the same formula,
  // only this time over integer variables a,b,c
  
  // We staart by reseting the solver to flush
  // previous assertions.
  solver.reset();

  // Next, we assert the same assertions above with integers,
  // in an abbreviated manner.
  solver.assertFormula(
        solver.mkTerm(LEQ, solver.mkInteger(0), solver.mkTerm(DIV, solver.mkTerm(PLUS, a, b), solver.mkInteger(2))));
  solver.assertFormula(
        solver.mkTerm(LEQ, c, solver.mkInteger(2)));
  solver.assertFormula(
        solver.mkTerm(LT, solver.mkTerm(PLUS, a, b), solver.mkTerm(MULT, solver.mkInteger(2), c))
      );
  // We check whether the revised assertion is satisfiable.
  Result r = solver.checkSat();

  // This time the formula is unsatisfiable
  std::cout << "result: " << r << std::endl;

  // Obviously, we cannot get values for a,b,c, as
  // no values exist that make the formula true.
  // However, we can query the solver
  // for an unsatisfiable core, i.e., a subset
  // of the assertions that is already unsatisfiable.
  std::vector<Term> unsatCore = solver.getUnsatCore();
  std::cout << "unsat core size: " << unsatCore.size();
  std::cout << "unsat core: " << std::endl;
  for (const Term & t : unsatCore) {
    std::cout << t << std::endl;
  }

  return 0;
}
