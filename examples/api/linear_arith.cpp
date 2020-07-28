/*********************                                                        */
/*! \file linear_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the linear arithmetic capabilities of CVC4
 **
 ** A simple demonstration of the linear arithmetic solving capabilities and
 ** the push pop of CVC4. This also gives an example option.
 **/

#include <iostream>

#include "cvc4/api/cvc4cpp.h"

using namespace std;
using namespace CVC4::api;

int main()
{
  Solver slv;
  slv.setLogic("QF_LIRA"); // Set the logic

  // Prove that if given x (Integer) and y (Real) then
  // the maximum value of y - x is 2/3

  // Sorts
  Sort real = slv.getRealSort();
  Sort integer = slv.getIntegerSort();

  // Variables
  Term x = slv.mkConst(integer, "x");
  Term y = slv.mkConst(real, "y");

  // Constants
  Term three = slv.mkReal(3);
  Term neg2 = slv.mkReal(-2);
  Term two_thirds = slv.mkReal(2, 3);

  // Terms
  Term three_y = slv.mkTerm(MULT, three, y);
  Term diff = slv.mkTerm(MINUS, y, x);

  // Formulas
  Term x_geq_3y = slv.mkTerm(GEQ, x, three_y);
  Term x_leq_y = slv.mkTerm(LEQ, x, y);
  Term neg2_lt_x = slv.mkTerm(LT, neg2, x);

  Term assertions =
    slv.mkTerm(AND, x_geq_3y, x_leq_y, neg2_lt_x);

  cout << "Given the assertions " << assertions << endl;
  slv.assertFormula(assertions);


  slv.push();
  Term diff_leq_two_thirds = slv.mkTerm(LEQ, diff, two_thirds);
  cout << "Prove that " << diff_leq_two_thirds << " with CVC4." << endl;
  cout << "CVC4 should report ENTAILED." << endl;
  cout << "Result from CVC4 is: " << slv.checkEntailed(diff_leq_two_thirds)
       << endl;
  slv.pop();

  cout << endl;

  slv.push();
  Term diff_is_two_thirds = slv.mkTerm(EQUAL, diff, two_thirds);
  slv.assertFormula(diff_is_two_thirds);
  cout << "Show that the assertions are consistent with " << endl;
  cout << diff_is_two_thirds << " with CVC4." << endl;
  cout << "CVC4 should report SAT." << endl;
  cout << "Result from CVC4 is: " << slv.checkSat() << endl;
  slv.pop();

  cout << "Thus the maximum value of (y - x) is 2/3."<< endl;

  return 0;
}
