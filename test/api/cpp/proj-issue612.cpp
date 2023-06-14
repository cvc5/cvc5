/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-models", "true");
  Sort s0 = solver.getRealSort();
  Term t1 = solver.mkConst(s0, "_x0");
  Term t2 = solver.mkReal(181067, 804);
  Term t3 = solver.mkConst(s0, "_x1");
  Term t4 = solver.mkTerm(SET_SINGLETON, {t1});
  Sort s5 = t4.getSort();
  Term t6 = solver.mkTerm(SET_COMPLEMENT, {t4});
  Op o7 = solver.mkOp(REGEXP_ALLCHAR);
  Term t8 = solver.mkTerm(o7, {});
  Sort s9 = t8.getSort();
  Term t10 = solver.mkTerm(SET_SINGLETON, {t1});
  Term t11 = solver.mkVar(s0, "_f2_0");
  Term t12 = solver.mkVar(s5, "_f2_1");
  Term t13 = solver.mkVar(s0, "_f2_2");
  Term t14 = solver.mkVar(s0, "_f2_3");
  Op o15 = solver.mkOp(SET_CHOOSE);
  Term t16 = solver.mkTerm(o15, {t12});
  Term t17 = solver.mkPi();
  Op o18 = solver.mkOp(ARCCOSECANT);
  Term t19 = solver.mkTerm(o18, {t2});
  Op o20 = solver.mkOp(SET_CHOOSE);
  Term t21 = solver.mkTerm(o15, {t4});
  Op o22 = solver.mkOp(DIVISION);
  Term t23 = solver.mkTerm(o22, {t1, t11});
  Op o24 = solver.mkOp(SUB);
  Term t25 = solver.mkTerm(o24, {t14, t13});
  Op o26 = solver.mkOp(NEG);
  Term t27 = solver.mkTerm(o26, {t1});
  Op o28 = solver.mkOp(ARCSECANT);
  Term t29 = solver.mkTerm(o28, {t1});
  Op o30 = solver.mkOp(SUB);
  Term t31 = solver.mkTerm(o24, {t1, t1});
  Op o32 = solver.mkOp(SUB);
  Term t33 = solver.mkTerm(o24, {t1, t14});
  Op o34 = solver.mkOp(DIVISION);
  Term t35 = solver.mkTerm(o22, {t1, t1});
  Op o36 = solver.mkOp(ARCSINE);
  Term t37 = solver.mkTerm(o36, {t1});
  Op o38 = solver.mkOp(NEG);
  Term t39 = solver.mkTerm(o26, {t1});
  Op o40 = solver.mkOp(DIVISION);
  Term t41 = solver.mkTerm(o22, {t1, t1});
  Op o42 = solver.mkOp(SET_CHOOSE);
  Term t43 = solver.mkTerm(o15, {t4});
  Op o44 = solver.mkOp(SUB);
  Term t45 = solver.mkTerm(o24, {t11, t1});
  Op o46 = solver.mkOp(SET_CHOOSE);
  Term t47 = solver.mkTerm(o15, {t4});
  Op o48 = solver.mkOp(SET_CHOOSE);
  Term t49 = solver.mkTerm(o15, {t4});
  Op o50 = solver.mkOp(ARCSINE);
  Term t51 = solver.mkTerm(o36, {t1});
  Op o52 = solver.mkOp(DIVISION);
  Term t53 = solver.mkTerm(o22, {t1, t1});
  Op o54 = solver.mkOp(ADD);
  Term t55 = solver.mkTerm(o54, {t14, t1});
  Op o56 = solver.mkOp(SET_CHOOSE);
  Term t57 = solver.mkTerm(o15, {t4});
  Op o58 = solver.mkOp(ARCCOTANGENT);
  Term t59 = solver.mkTerm(o58, {t1});
  Op o60 = solver.mkOp(SET_CHOOSE);
  Term t61 = solver.mkTerm(o15, {t4});
  Op o62 = solver.mkOp(LT);
  Term t63 = solver.mkTerm(o62, {t1, t29, t29});
  Sort s64 = t63.getSort();
  Op o65 = solver.mkOp(NOT);
  Term t66 = solver.mkTerm(o65, {t63});
  Term t67 = solver.mkTerm(REGEXP_INTER, {t8, t8});
  solver.assertFormula(t66);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
