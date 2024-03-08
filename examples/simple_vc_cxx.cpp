/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the C++ interface
 *
 * Compare to the Java interface in SimpleVC.java; they are virtually
 * line-by-line identical.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);

  // Prove that for integers x and y:
  //   x > 0 AND y > 0  =>  2x + y >= 3

  Sort integer = tm.getIntegerSort();

  Term x = tm.mkConst(integer, "x");
  Term y = tm.mkConst(integer, "y");
  Term zero = tm.mkInteger(0);

  Term x_positive = tm.mkTerm(Kind::GT, {x, zero});
  Term y_positive = tm.mkTerm(Kind::GT, {y, zero});

  Term two = tm.mkInteger(2);
  Term twox = tm.mkTerm(Kind::MULT, {two, x});
  Term twox_plus_y = tm.mkTerm(Kind::ADD, {twox, y});

  Term three = tm.mkInteger(3);
  Term twox_plus_y_geq_3 = tm.mkTerm(Kind::GEQ, {twox_plus_y, three});

  Term formula = tm.mkTerm(Kind::AND, {x_positive, y_positive})
                     .impTerm(twox_plus_y_geq_3);

  std::cout << "Checking entailment of formula " << formula << " with cvc5."
            << std::endl;
  std::cout << "cvc5 should report UNSAT." << std::endl;
  std::cout << "Result from cvc5 is: "
            << slv.checkSatAssuming(formula.notTerm()) << std::endl;

  return 0;
}
