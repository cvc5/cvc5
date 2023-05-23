/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for issue #6111
 *
 */
#include <cvc5/cvc5.h>

#include <iostream>
#include <vector>

using namespace cvc5;
using namespace std;

int main()
{
  Solver solver;
  solver.setLogic("QF_BV");
  Sort bvsort12979 = solver.mkBitVectorSort(12979);
  Term input2_1 = solver.mkConst(bvsort12979, "intpu2_1");
  Term zero = solver.mkBitVector(bvsort12979.getBitVectorSize(), "0", 10);

  vector<Term> args1;
  args1.push_back(zero);
  args1.push_back(input2_1);
  Term bvult_res = solver.mkTerm(BITVECTOR_ULT, {args1});
  solver.assertFormula(bvult_res);

  Sort bvsort4 = solver.mkBitVectorSort(4);
  Term concat_result_42 = solver.mkConst(bvsort4, "concat_result_42");
  Sort bvsort8 = solver.mkBitVectorSort(8);
  Term concat_result_43 = solver.mkConst(bvsort8, "concat_result_43");

  vector<Term> args2;
  args2.push_back(concat_result_42);
  args2.push_back(solver.mkTerm(solver.mkOp(BITVECTOR_EXTRACT, {7, 4}),
                                {concat_result_43}));
  solver.assertFormula(solver.mkTerm(EQUAL, {args2}));

  vector<Term> args3;
  args3.push_back(concat_result_42);
  args3.push_back(solver.mkTerm(solver.mkOp(BITVECTOR_EXTRACT, {3, 0}),
                                {concat_result_43}));
  solver.assertFormula(solver.mkTerm(EQUAL, {args3}));

  cout << solver.checkSat() << endl;

  return 0;
}
