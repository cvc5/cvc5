/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the linear arithmetic solving capabilities and
 * the push pop of cvc5. This also gives an example option.
 */

#include <iostream>

#include <cvc5/cvc5.h>

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_LIRA"); // Set the logic

  // Prove that if given x (Integer) and y (Real) then
  // the maximum value of y - x is 2/3

  // Sorts
  Sort real = tm.getRealSort();
  Sort integer = tm.getIntegerSort();

  // Variables
  Term x = tm.mkConst(integer, "x");
  Term y = tm.mkConst(real, "y");

  // Constants
  Term three = tm.mkInteger(3);
  Term neg2 = tm.mkInteger(-2);
  Term two_thirds = tm.mkReal(2, 3);

  // Terms
  Term three_y = tm.mkTerm(Kind::MULT, {three, y});
  Term diff = tm.mkTerm(Kind::SUB, {y, x});

  // Formulas
  Term x_geq_3y = tm.mkTerm(Kind::GEQ, {x, three_y});
  Term x_leq_y = tm.mkTerm(Kind::LEQ, {x, y});
  Term neg2_lt_x = tm.mkTerm(Kind::LT, {neg2, x});

  Term assertions = tm.mkTerm(Kind::AND, {x_geq_3y, x_leq_y, neg2_lt_x});

  cout << "Given the assertions " << assertions << endl;
  slv.assertFormula(assertions);


  slv.push();
  Term diff_leq_two_thirds = tm.mkTerm(Kind::LEQ, {diff, two_thirds});
  cout << "Prove that " << diff_leq_two_thirds << " with cvc5." << endl;
  cout << "cvc5 should report UNSAT." << endl;
  cout << "Result from cvc5 is: "
       << slv.checkSatAssuming(diff_leq_two_thirds.notTerm()) << endl;
  slv.pop();

  cout << endl;

  slv.push();
  Term diff_is_two_thirds = tm.mkTerm(Kind::EQUAL, {diff, two_thirds});
  slv.assertFormula(diff_is_two_thirds);
  cout << "Show that the assertions are consistent with " << endl;
  cout << diff_is_two_thirds << " with cvc5." << endl;
  cout << "cvc5 should report SAT." << endl;
  cout << "Result from cvc5 is: " << slv.checkSat() << endl;
  slv.pop();

  cout << "Thus the maximum value of (y - x) is 2/3."<< endl;

  return 0;
}
