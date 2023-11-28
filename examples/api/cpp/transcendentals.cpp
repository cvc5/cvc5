/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
  Solver slv;
  slv.setLogic("QF_NRAT");

  Sort real = slv.getRealSort();

  // Variables
  Term x = slv.mkConst(real, "x");
  Term y = slv.mkConst(real, "y");

  // Helper terms
  Term two = slv.mkReal(2);
  Term pi = slv.mkPi();
  Term twopi = slv.mkTerm(Kind::MULT, {two, pi});
  Term ysq = slv.mkTerm(Kind::MULT, {y, y});
  Term sinx = slv.mkTerm(Kind::SINE, {x});

  // Formulas
  Term x_gt_pi = slv.mkTerm(Kind::GT, {x, pi});
  Term x_lt_tpi = slv.mkTerm(Kind::LT, {x, twopi});
  Term ysq_lt_sinx = slv.mkTerm(Kind::LT, {ysq, sinx});

  slv.assertFormula(x_gt_pi);
  slv.assertFormula(x_lt_tpi);
  slv.assertFormula(ysq_lt_sinx);

  cout << "cvc5 should report UNSAT." << endl;
  cout << "Result from cvc5 is: " << slv.checkSat() << endl;

  return 0;
}
