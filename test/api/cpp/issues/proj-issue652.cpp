/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #652
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("sep-pre-skolem-emp", "true");
  Sort s0 = tm.getIntegerSort();
  Term t1 = tm.mkConst(s0, "_x1");
  Term t2 = tm.mkConst(s0, "_x8");
  Term t3 = tm.mkConst(s0, "_x10");
  Term t4 = tm.mkTerm(Kind::SEQ_UNIT, {t1});
  Sort s5 = t4.getSort();
  Term t6 = tm.mkVar(s5, "_f13_0");
  Term t7 = tm.mkTerm(Kind::SEQ_REPLACE_ALL, {t4, t4, t6});
  Term t8 = tm.mkTerm(Kind::SEQ_AT, {t4, t1});
  Term t9 = tm.mkTerm(Kind::SEQ_UPDATE, {t8, t1, t8});
  Term t10 = tm.mkTerm(Kind::SEQ_EXTRACT, {t4, t1, t2});
  Term t11 = tm.mkTerm(Kind::SEQ_REPLACE, {t10, t9, t7});
  Sort s12 = tm.mkFunctionSort({s5}, s5);
  Term t13 = solver.defineFun("_f13", {t6}, s5, t11, true);
  Op o14 = tm.mkOp(Kind::APPLY_UF);
  Term t15 = tm.mkTerm(o14, {t13, t4});
  Term t16 = tm.mkTerm(Kind::APPLY_UF, {t13, t15});
  Op o17 = tm.mkOp(Kind::SEQ_EXTRACT);
  Term t18 = tm.mkTerm(o17, {t16, t3, t1});
  Op o19 = tm.mkOp(Kind::SEQ_PREFIX);
  Term t20 = tm.mkTerm(o19, {t18, t4});
  Sort s21 = t20.getSort();
  Term t22 = t20.impTerm(t20);
  solver.assertFormula(t22);
  solver.checkSat();

  return 0;
}
