/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #671
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("inst-max-level", "6067390630711104712");
  solver.setOption("produce-abducts", "true");
  Sort s0 = tm.getStringSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = tm.mkConst(s0, "_x4");
  Term t3 = tm.mkString("");
  Term t4 = tm.mkConst(s0, "_x8");
  Term t5 = tm.mkConst(s0, "_x9");
  Op o6 = tm.mkOp(Kind::STRING_REV);
  Term t7 = tm.mkTerm(o6, {t4});
  Op o8 = tm.mkOp(Kind::EQUAL);
  Term t9 = tm.mkTerm(o8, {t7, t2});
  Sort s10 = t9.getSort();
  Term t11 = tm.mkTerm(Kind::STRING_LEQ, {t1, t4});
  Term t12 = tm.mkTerm(Kind::STRING_LT, {t3, t5});
  Term t13 = tm.mkTerm(Kind::ITE, {t11, t9, t9});
  solver.assertFormula(t13);
  Term t14 = solver.getAbduct(t12);

  return 0;
}
