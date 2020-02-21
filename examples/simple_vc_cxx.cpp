/*********************                                                        */
/*! \file simple_vc_cxx.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the C++ interface
 **
 ** A simple demonstration of the C++ interface.  Compare to the Java
 ** interface in SimpleVC.java; they are virtually line-by-line
 ** identical.
 **/

#include <iostream>

#include <cvc4/cvc4.h>

using namespace std;
using namespace CVC4;

int main() {

  ExprManager em;
  SmtEngine smt(&em);
  smt.setOption("produce-models", "true");
  // smt.setOption("debug", "arith");
  smt.setOption("trace", "integers");
  // smt.setOption("trace", "amalee");


  Type integer = em.integerType();

  Expr y = em.mkVar("y", integer);
  Expr x = em.mkVar("x", integer);

  Expr one = em.mkConst(Rational(1));

  Expr zero = em.mkConst(Rational(0));

  Expr slope = em.mkConst(Rational::fromDecimal("1.93"));
  Expr intercept1 = em.mkConst(Rational::fromDecimal("25.7"));
  Expr intercept2 = em.mkConst(Rational::fromDecimal("4.9"));
  Expr intercept3 = em.mkConst(Rational::fromDecimal("15.9"));
  Expr intercept4 = em.mkConst(Rational::fromDecimal("17.5"));

  Expr l1 = em.mkExpr(kind::MULT, slope, x);
  l1 = em.mkExpr(kind::PLUS, y, l1);
  l1 = em.mkExpr(kind::MINUS, l1, intercept1);
  l1 = em.mkExpr(kind::LEQ, l1, zero);


  cout << "Checking satisfiability of formula " << l1 << " with CVC4." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(l1) << endl;
  cout << "x is " << smt.getValue(x) << ", y is " << smt.getValue(y) << endl;


  Expr l2 = em.mkExpr(kind::MULT, slope, x);
  l2 = em.mkExpr(kind::MINUS, y, l2);
  l2 = em.mkExpr(kind::MINUS, l2, intercept2);
  l2 = em.mkExpr(kind::GEQ, l2, zero);


  cout << "Checking satisfiability of formula " << l2 << " with CVC4." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(l2) << endl;
  cout << "x is " << smt.getValue(x) << ", y is " << smt.getValue(y) << endl;

  Expr l3 = em.mkExpr(kind::MULT, slope, x);
  l3 = em.mkExpr(kind::MINUS, y, l3);
  l3 = em.mkExpr(kind::MINUS, l3, intercept3);
  l3 = em.mkExpr(kind::LEQ, l3, zero);


  cout << "Checking satisfiability of formula " << l3 << " with CVC4." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(l3) << endl;
  cout << "x is " << smt.getValue(x) << ", y is " << smt.getValue(y) << endl;

  Expr l4 = em.mkExpr(kind::MULT, slope, x);
  l4 = em.mkExpr(kind::PLUS, y, l4);
  l4 = em.mkExpr(kind::MINUS, l4, intercept4);
  l4 = em.mkExpr(kind::GEQ, l4, zero);


  cout << "Checking satisfiability of formula " << l4 << " with CVC4." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(l4) << endl;
  cout << "x is " << smt.getValue(x) << ", y is " << smt.getValue(y) << endl;



  Expr all_ands = em.mkExpr(kind::AND, l4, em.mkExpr(kind::AND, l3, em.mkExpr(kind::AND, l1, l2)));
  cout << "Checking satisfiability of formula " << all_ands << " with CVC4." << endl;
  cout << "Result from CVC4 is: " << smt.checkSat(all_ands) << endl;
  cout << "x is " << smt.getValue(x) << ", y is " << smt.getValue(y) << endl;

  // Prove that for integers x and y:
  //   x > 0 AND y > 0  =>  2x + y >= 3


  // Expr y1 = em.mkVar("y1", integer);
  // Expr y2 = em.mkVar("y2", integer);
  // Expr zero = em.mkConst(Rational(0));

  // Expr one = em.mkConst(Rational(1));


  // Expr y0_positive = em.mkExpr(kind::GEQ, y0, zero);
  // Expr y1_positive = em.mkExpr(kind::GEQ, y1, zero);
  // Expr y2_positive = em.mkExpr(kind::GEQ, y2, zero);


  // Expr y0_lteone = em.mkExpr(kind::LEQ, y0, one);
  // Expr y1_lteone = em.mkExpr(kind::LEQ, y1, one);
  // Expr y2_lteone = em.mkExpr(kind::LEQ, y2, one);

  // Expr and0 = em.mkExpr(kind::AND, y0_positive, y0_lteone);
  // Expr and1 = em.mkExpr(kind::AND, y1_positive, y1_lteone);
  // Expr and2 = em.mkExpr(kind::AND, y2_positive, y2_lteone);

  // Expr dist = em.mkExpr(kind::DISTINCT, y0, y1, y2);

  // Expr formula = em.mkExpr(kind::AND, and0, em.mkExpr(kind::AND, and1, em.mkExpr(kind::AND, and2, dist)));






  // Expr y_positive = em.mkExpr(kind::GT, y, zero);

  // Expr two = em.mkConst(Rational(2));
  // Expr twox = em.mkExpr(kind::MULT, two, x);
  // Expr twox_plus_y = em.mkExpr(kind::PLUS, twox, y);

  // Expr three = em.mkConst(Rational(3));
  // Expr twox_plus_y_geq_3 = em.mkExpr(kind::GEQ, twox_plus_y, three);

  // Expr formula =
  //   em.mkExpr(kind::AND, x_positive, y_positive).
  //   impExpr(twox_plus_y_geq_3);



  return 0;
}
