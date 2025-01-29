/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the transcendental extension.
 */

#include <iostream>

#include <cvc5/cvc5.h>

using namespace std;
using namespace cvc5;

int main()
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_NRAT");

  Sort real = tm.getRealSort();

  // Variables
  Term x = tm.mkConst(real, "x");
  Term y = tm.mkConst(real, "y");

  // Helper terms
  Term two = tm.mkReal(2);
  Term pi = tm.mkPi();
  Term twopi = tm.mkTerm(Kind::MULT, {two, pi});
  Term ysq = tm.mkTerm(Kind::MULT, {y, y});
  Term sinx = tm.mkTerm(Kind::SINE, {x});

  // Formulas
  Term x_gt_pi = tm.mkTerm(Kind::GT, {x, pi});
  Term x_lt_pi = tm.mkTerm(Kind::LT, {x, twopi});
  Term ysq_lt_sinx = tm.mkTerm(Kind::LT, {ysq, sinx});

  slv.assertFormula(x_gt_pi);
  slv.assertFormula(x_lt_pi);
  slv.assertFormula(ysq_lt_sinx);

  cout << "cvc5 should report UNSAT." << endl;
  cout << "Result from cvc5 is: " << slv.checkSat() << endl;

  return 0;
}
