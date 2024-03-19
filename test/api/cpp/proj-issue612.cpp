/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #612
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("produce-models", "true");
  Sort s0 = tm.getRealSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = tm.mkReal(181067, 804);
  Term t3 = tm.mkConst(s0, "_x1");
  Term t4 = tm.mkTerm(Kind::SET_SINGLETON, {t1});
  Sort s5 = t4.getSort();
  Term t6 = tm.mkTerm(Kind::SET_COMPLEMENT, {t4});
  Op o7 = tm.mkOp(Kind::REGEXP_ALLCHAR);
  Term t8 = tm.mkTerm(o7, {});
  Sort s9 = t8.getSort();
  Term t10 = tm.mkTerm(Kind::SET_SINGLETON, {t1});
  Term t11 = tm.mkVar(s0, "_f2_0");
  Term t12 = tm.mkVar(s5, "_f2_1");
  Term t13 = tm.mkVar(s0, "_f2_2");
  Term t14 = tm.mkVar(s0, "_f2_3");
  Op o15 = tm.mkOp(Kind::SET_CHOOSE);
  Term t16 = tm.mkTerm(o15, {t12});
  Term t17 = tm.mkPi();
  Op o18 = tm.mkOp(Kind::ARCCOSECANT);
  Term t19 = tm.mkTerm(o18, {t2});
  Op o20 = tm.mkOp(Kind::SET_CHOOSE);
  Term t21 = tm.mkTerm(o15, {t4});
  Op o22 = tm.mkOp(Kind::DIVISION);
  Term t23 = tm.mkTerm(o22, {t1, t11});
  Op o24 = tm.mkOp(Kind::SUB);
  Term t25 = tm.mkTerm(o24, {t14, t13});
  Op o26 = tm.mkOp(Kind::NEG);
  Term t27 = tm.mkTerm(o26, {t1});
  Op o28 = tm.mkOp(Kind::ARCSECANT);
  Term t29 = tm.mkTerm(o28, {t1});
  Op o30 = tm.mkOp(Kind::SUB);
  Term t31 = tm.mkTerm(o24, {t1, t1});
  Op o32 = tm.mkOp(Kind::SUB);
  Term t33 = tm.mkTerm(o24, {t1, t14});
  Op o34 = tm.mkOp(Kind::DIVISION);
  Term t35 = tm.mkTerm(o22, {t1, t1});
  Op o36 = tm.mkOp(Kind::ARCSINE);
  Term t37 = tm.mkTerm(o36, {t1});
  Op o38 = tm.mkOp(Kind::NEG);
  Term t39 = tm.mkTerm(o26, {t1});
  Op o40 = tm.mkOp(Kind::DIVISION);
  Term t41 = tm.mkTerm(o22, {t1, t1});
  Op o42 = tm.mkOp(Kind::SET_CHOOSE);
  Term t43 = tm.mkTerm(o15, {t4});
  Op o44 = tm.mkOp(Kind::SUB);
  Term t45 = tm.mkTerm(o24, {t11, t1});
  Op o46 = tm.mkOp(Kind::SET_CHOOSE);
  Term t47 = tm.mkTerm(o15, {t4});
  Op o48 = tm.mkOp(Kind::SET_CHOOSE);
  Term t49 = tm.mkTerm(o15, {t4});
  Op o50 = tm.mkOp(Kind::ARCSINE);
  Term t51 = tm.mkTerm(o36, {t1});
  Op o52 = tm.mkOp(Kind::DIVISION);
  Term t53 = tm.mkTerm(o22, {t1, t1});
  Op o54 = tm.mkOp(Kind::ADD);
  Term t55 = tm.mkTerm(o54, {t14, t1});
  Op o56 = tm.mkOp(Kind::SET_CHOOSE);
  Term t57 = tm.mkTerm(o15, {t4});
  Op o58 = tm.mkOp(Kind::ARCCOTANGENT);
  Term t59 = tm.mkTerm(o58, {t1});
  Op o60 = tm.mkOp(Kind::SET_CHOOSE);
  Term t61 = tm.mkTerm(o15, {t4});
  Op o62 = tm.mkOp(Kind::LT);
  Term t63 = tm.mkTerm(o62, {t1, t29, t29});
  Sort s64 = t63.getSort();
  Op o65 = tm.mkOp(Kind::NOT);
  Term t66 = tm.mkTerm(o65, {t63});
  Term t67 = tm.mkTerm(Kind::REGEXP_INTER, {t8, t8});
  solver.assertFormula(t66);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
