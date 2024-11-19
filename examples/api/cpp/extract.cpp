/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Clark Barrett, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_BV"); // Set the logic

  Sort bv32 = tm.mkBitVectorSort(32);

  Term x = tm.mkConst(bv32, "x");

  Op ext_31_1 = tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 1});
  Term x_31_1 = tm.mkTerm(ext_31_1, {x});

  Op ext_30_0 = tm.mkOp(Kind::BITVECTOR_EXTRACT, {30, 0});
  Term x_30_0 = tm.mkTerm(ext_30_0, {x});

  Op ext_31_31 = tm.mkOp(Kind::BITVECTOR_EXTRACT, {31, 31});
  Term x_31_31 = tm.mkTerm(ext_31_31, {x});

  Op ext_0_0 = tm.mkOp(Kind::BITVECTOR_EXTRACT, {0, 0});
  Term x_0_0 = tm.mkTerm(ext_0_0, {x});

  Term eq = tm.mkTerm(Kind::EQUAL, {x_31_1, x_30_0});
  cout << " Asserting: " << eq << endl;
  slv.assertFormula(eq);

  Term dis = tm.mkTerm(Kind::DISTINCT, {x_31_31, x_0_0});
  cout << " Check sat assuming: " << dis << endl;
  cout << " Expect UNSAT." << endl;
  cout << " cvc5: " << slv.checkSatAssuming(dis) << endl;

  return 0;
}
