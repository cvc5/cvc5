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
 * Test for project issue #574
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-models", "true");
  Sort s0 = solver.mkUninterpretedSort("_u0");
  Sort s1 = solver.getBooleanSort();
  Sort s2 = solver.getBooleanSort();
  Sort s3 = solver.mkUninterpretedSort("_u1");
  Term t4 = solver.mkConst(s0, "_x2");
  Term t5 = solver.mkConst(s3, "_x3");
  Term t6 = solver.mkConst(s0, "_x4");
  Term t7 = solver.mkConst(s0, "_x5");
  Term t8 = solver.mkConst(s0, "_x6");
  Term t9 = solver.mkVar(s3, "_x7");
  Term t10 = solver.mkConst(s0, "_x8");
  Term t11 = solver.mkConst(s3, "_x9");
  Sort s12 = solver.mkArraySort(s0, s0);
  Term t13 = solver.mkConst(s3, "_x10");
  Term t14 = solver.mkConst(s0, "_x11");
  Term t15 = solver.mkVar(s0, "_x12");
  Term t16 = solver.mkVar(s12, "_x13");
  Term t17 = solver.mkConst(s0, "_x14");
  Term t18 = solver.mkVar(s0, "_x19");
  Term t19 = solver.mkVar(s0, "_x20");
  Term t20 = solver.mkConst(s3, "_x21");
  Term t21 = solver.mkConst(s3, "_x22");
  Term t22 = solver.mkConst(s12, "_x27");
  Term t23 = solver.mkConst(s12, "_x28");
  Term t24 = solver.mkConst(s1, "_x29");
  Term t25 = solver.mkConst(s12, "_x30");
  Term t26 = solver.mkTrue();
  Op o27 = solver.mkOp(AND);
  Term t28 = solver.mkTerm(o27, {t24, t26});
  Term t29 = solver.mkTerm(XOR, {t24, t24});
  Term t30 = solver.mkPi();
  Sort s31 = t30.getSort();
  Term t32 = solver.mkPi();
  Op o33 = solver.mkOp(STORE);
  Term t34 = solver.mkTerm(o33, {t16, t18, t4});
  Op o35 = solver.mkOp(ARCCOSINE);
  Term t36 = solver.mkTerm(o35, {t30});
  Term t37 = solver.mkTerm(SELECT, {t22, t4});
  Op o38 = solver.mkOp(ITE);
  Term t39 = t24.iteTerm(t24, t24);
  Op o40 = solver.mkOp(COSECANT);
  Term t41 = solver.mkTerm(o40, {t30});
  Op o42 = solver.mkOp(ARCSECANT);
  Term t43 = solver.mkTerm(o42, {t30});
  Op o44 = solver.mkOp(GEQ);
  Term t45 = solver.mkTerm(o44, {t43, t30});
  Term t46 = solver.mkTerm(NEG, {t30});
  Term t47 = t45.eqTerm(t45);
  solver.assertFormula(t47);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
