/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the solving capabilities of the cvc5
 * bit-vector solver.
 *
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace std;
using namespace cvc5;

int main()
{
  Solver slv;
  slv.setLogic("QF_BV"); // Set the logic

  Sort bitvector32 = slv.mkBitVectorSort(32);

  Term x = slv.mkConst(bitvector32, "a");

  Op ext_31_1 = slv.mkOp(BITVECTOR_EXTRACT, {31, 1});
  Term x_31_1 = slv.mkTerm(ext_31_1, {x});

  Op ext_30_0 = slv.mkOp(BITVECTOR_EXTRACT, {30, 0});
  Term x_30_0 = slv.mkTerm(ext_30_0, {x});

  Op ext_31_31 = slv.mkOp(BITVECTOR_EXTRACT, {31, 31});
  Term x_31_31 = slv.mkTerm(ext_31_31, {x});

  Op ext_0_0 = slv.mkOp(BITVECTOR_EXTRACT, {0, 0});
  Term x_0_0 = slv.mkTerm(ext_0_0, {x});

  Term eq = slv.mkTerm(EQUAL, {x_31_1, x_30_0});
  cout << " Asserting: " << eq << endl;
  slv.assertFormula(eq);

  Term eq2 = slv.mkTerm(EQUAL, {x_31_31, x_0_0});
  cout << " Check sat assuming: " << eq2.notTerm() << endl;
  cout << " Expect UNSAT. " << endl;
  cout << " cvc5: " << slv.checkSatAssuming(eq2.notTerm()) << endl;

  return 0;
}
