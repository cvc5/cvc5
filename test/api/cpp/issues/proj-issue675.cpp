/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #675
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("ite-simp", "true");
  solver.setOption("fp-exp", "true");
  solver.setOption("produce-interpolants", "true");
  Sort s0 = tm.mkFloatingPointSort(5, 11);
  Sort s1 = tm.mkBitVectorSort(16);
  Term t2 = tm.mkConst(s1, "_x15");
  Term t3 = tm.mkConst(s0, "_x16");
  Term t4 = tm.mkConst(s1, "_x18");
  Term t5 = tm.mkTerm(Kind::EQUAL, {t4, t2});
  Sort s6 = t5.getSort();
  Term t7 = tm.mkVar(s0, "_f22_0");
  Term t8 = tm.mkVar(s6, "_f22_1");
  Sort s9 = tm.mkFunctionSort({s0, s6}, s0);
  Term t10 = solver.defineFun("_f22", {t7, t8}, s0, t3, true);
  Op o11 = tm.mkOp(Kind::FLOATINGPOINT_REM);
  Term t12 = tm.mkTerm(o11, {t3, t3});
  Term t13 = t5.iteTerm(t3, t12);
  solver.assertFormula(t5);
  Term t14 = tm.mkTerm(Kind::FLOATINGPOINT_IS_ZERO, {t13});
  Term t15 = solver.getInterpolant(t14);

  return 0;
}
