/*********************                                                        */
/*! \file linear_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;

int main() {
  ExprManager em;
  SmtEngine smt(&em);
  smt.setLogic("QF_LIRA"); // Set the logic

  // Prove that if given x (Integer) and y (Real) then
  // the maximum value of y - x is 2/3

  // Types
  Type real = em.realType();
  Type integer = em.integerType();

  // Variables
  Expr x = em.mkVar("x", integer);
  Expr y = em.mkVar("y", real);

  // Constants
  Expr three = em.mkConst(Rational(3));
  Expr neg2 = em.mkConst(Rational(-2));
  Expr two_thirds = em.mkConst(Rational(2,3));

  // Terms
  Expr three_y = em.mkExpr(kind::MULT, three, y);
  Expr diff = em.mkExpr(kind::MINUS, y, x);

  // Formulas
  Expr x_geq_3y = em.mkExpr(kind::GEQ, x, three_y);
  Expr x_leq_y = em.mkExpr(kind::LEQ, x, y);
  Expr neg2_lt_x = em.mkExpr(kind::LT, neg2, x);

  Expr assumptions =
    em.mkExpr(kind::AND, x_geq_3y, x_leq_y, neg2_lt_x);

  cout << "Given the assumptions " << assumptions << endl;
  smt.assertFormula(assumptions);


  smt.push();
  Expr diff_leq_two_thirds = em.mkExpr(kind::LEQ, diff, two_thirds);
  cout << "Prove that " << diff_leq_two_thirds << " with CVC4." << endl;
  cout << "CVC4 should report VALID." << endl;
  cout << "Result from CVC4 is: " << smt.query(diff_leq_two_thirds) << endl;
  smt.pop();

  cout << endl;

  smt.push();
  Expr diff_is_two_thirds = em.mkExpr(kind::EQUAL, diff, two_thirds);
  smt.assertFormula(diff_is_two_thirds);
  cout << "Show that the asserts are consistent with " << endl;
  cout << diff_is_two_thirds << " with CVC4." << endl;
  cout << "CVC4 should report SAT." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(em.mkConst(true)) << endl;
  smt.pop();

  cout << "Thus the maximum value of (y - x) is 2/3."<< endl;

  return 0;
}
