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
 * Test for project issue #574
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
  Sort s0 = tm.mkUninterpretedSort("_u0");
  Sort s1 = tm.getBooleanSort();
  Sort s2 = tm.getBooleanSort();
  Sort s3 = tm.mkUninterpretedSort("_u1");
  Term t4 = tm.mkConst(s0, "_x2");
  Term t5 = tm.mkConst(s3, "_x3");
  Term t6 = tm.mkConst(s0, "_x4");
  Term t7 = tm.mkConst(s0, "_x5");
  Term t8 = tm.mkConst(s0, "_x6");
  Term t9 = tm.mkVar(s3, "_x7");
  Term t10 = tm.mkConst(s0, "_x8");
  Term t11 = tm.mkConst(s3, "_x9");
  Sort s12 = tm.mkArraySort(s0, s0);
  Term t13 = tm.mkConst(s3, "_x10");
  Term t14 = tm.mkConst(s0, "_x11");
  Term t15 = tm.mkVar(s0, "_x12");
  Term t16 = tm.mkVar(s12, "_x13");
  Term t17 = tm.mkConst(s0, "_x14");
  Term t18 = tm.mkVar(s0, "_x19");
  Term t19 = tm.mkVar(s0, "_x20");
  Term t20 = tm.mkConst(s3, "_x21");
  Term t21 = tm.mkConst(s3, "_x22");
  Term t22 = tm.mkConst(s12, "_x27");
  Term t23 = tm.mkConst(s12, "_x28");
  Term t24 = tm.mkConst(s1, "_x29");
  Term t25 = tm.mkConst(s12, "_x30");
  Term t26 = tm.mkTrue();
  Op o27 = tm.mkOp(Kind::AND);
  Term t28 = tm.mkTerm(o27, {t24, t26});
  Term t29 = tm.mkTerm(Kind::XOR, {t24, t24});
  Term t30 = tm.mkPi();
  Sort s31 = t30.getSort();
  Term t32 = tm.mkPi();
  Op o33 = tm.mkOp(Kind::STORE);
  Term t34 = tm.mkTerm(o33, {t16, t18, t4});
  Op o35 = tm.mkOp(Kind::ARCCOSINE);
  Term t36 = tm.mkTerm(o35, {t30});
  Term t37 = tm.mkTerm(Kind::SELECT, {t22, t4});
  Op o38 = tm.mkOp(Kind::ITE);
  Term t39 = t24.iteTerm(t24, t24);
  Op o40 = tm.mkOp(Kind::COSECANT);
  Term t41 = tm.mkTerm(o40, {t30});
  Op o42 = tm.mkOp(Kind::ARCSECANT);
  Term t43 = tm.mkTerm(o42, {t30});
  Op o44 = tm.mkOp(Kind::GEQ);
  Term t45 = tm.mkTerm(o44, {t43, t30});
  Term t46 = tm.mkTerm(Kind::NEG, {t30});
  Term t47 = t45.eqTerm(t45);
  solver.assertFormula(t47);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
