/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #617
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setLogic("QF_NRA");
  solver.setOption("check-models", "true");
  Sort s0 = tm.getRealSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = tm.mkConst(s0, "_x1");
  Term t3 = tm.mkConst(s0, "_x2");
  Term t4 = tm.mkReal("6790089/71203");
  Term t5 = tm.mkReal("354131059765066077956502439364245754373025");
  Term t6 = tm.mkConst(s0, "_x3");
  Term t7 = tm.mkReal("640/79251919");
  Term t8 = tm.mkTerm(Kind::GT, {t2, t7});
  Sort s9 = t8.getSort();
  Op o10 = tm.mkOp(Kind::GT);
  Term t11 = tm.mkTerm(o10, {t2, t1});
  Op o12 = tm.mkOp(Kind::IMPLIES);
  Term t13 = tm.mkTerm(o12, {t8, t11, t8});
  Op o14 = tm.mkOp(Kind::MULT);
  Term t15 = tm.mkTerm(o14, {t1, t5, t6});
  Op o16 = tm.mkOp(Kind::NOT);
  Term t17 = tm.mkTerm(o16, {t13});
  solver.assertFormula(t13);
  Op o18 = tm.mkOp(Kind::DIVISION);
  Term t19 = tm.mkTerm(o18, {t15, t3});
  Op o20 = tm.mkOp(Kind::NEG);
  Term t21 = tm.mkTerm(o20, {t6});
  Op o22 = tm.mkOp(Kind::NEG);
  Term t23 = tm.mkTerm(o20, {t21});
  Op o24 = tm.mkOp(Kind::ITE);
  Term t25 = tm.mkTerm(o24, {t17, t13, t17});
  Term t26 = tm.mkTerm(Kind::NEG, {t23});
  Op o27 = tm.mkOp(Kind::ITE);
  Term t28 = t11.iteTerm(t26, t26);
  Op o29 = tm.mkOp(Kind::AND);
  Term t30 = t25.andTerm(t25);
  Term t31 = tm.mkTerm(Kind::NEG, {t28});
  Op o32 = tm.mkOp(Kind::ITE);
  Term t33 = tm.mkTerm(o24, {t30, t2, t31});
  Term t34 = tm.mkTerm(Kind::DIVISION, {t33, t31, t7});
  Op o35 = tm.mkOp(Kind::DIVISION);
  Term t36 = tm.mkTerm(o18, {t26, t6, t4, t34, t31});
  Term t37 = tm.mkTerm(Kind::NEG, {t36});
  Op o38 = tm.mkOp(Kind::GEQ);
  Term t39 = tm.mkTerm(o38, {t2, t2});
  Op o40 = tm.mkOp(Kind::ITE);
  Term t41 = tm.mkTerm(o24, {t39, t37, t2});
  Op o42 = tm.mkOp(Kind::LEQ);
  Term t43 = tm.mkTerm(o42, {t41, t31, t3});
  Op o44 = tm.mkOp(Kind::LEQ);
  Term t45 = tm.mkTerm(o42, {t2, t37, t19});
  Term t46 = tm.mkTerm(Kind::GT, {t1, t6});
  Term t47 = tm.mkTerm(Kind::LT, {t5, t23});
  Op o48 = tm.mkOp(Kind::ITE);
  Term t49 = tm.mkTerm(o24, {t46, t34, t31});
  Op o50 = tm.mkOp(Kind::GEQ);
  Term t51 = tm.mkTerm(o38, {t49, t21, t36});
  Term t52 = tm.mkTerm(Kind::XOR, {t47, t45});
  Op o53 = tm.mkOp(Kind::XOR);
  Term t54 = tm.mkTerm(o53, {t51, t52});
  solver.assertFormula(t43);
  solver.assertFormula(t54);
  solver.checkSat();

  return 0;
}
