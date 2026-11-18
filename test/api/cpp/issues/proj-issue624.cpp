/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #624
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
  solver.setOption("produce-models", "true");
  solver.setOption("incremental", "true");
  Sort s0 = tm.getRealSort();
  Sort s1 = tm.getBooleanSort();
  Sort s2 = tm.getRealSort();
  Term t3 = tm.mkConst(s1, "_x0");
  Term t4 = tm.mkConst(s0, "_x1");
  Term t5 = tm.mkReal(5, 2562);
  Term t6 = tm.mkTerm(Kind::GEQ, {t4, t5});
  Op o7 = tm.mkOp(Kind::IMPLIES);
  Term t8 = t6.impTerm(t6);
  Term t9 = tm.mkVar(s0, "_f2_0");
  Term t10 = tm.mkVar(s1, "_f2_1");
  Term t11 = tm.mkVar(s0, "_f2_2");
  Term t12 = tm.mkVar(s1, "_f2_3");
  Op o13 = tm.mkOp(Kind::GEQ);
  Term t14 = tm.mkTerm(o13, {t9, t11});
  Op o15 = tm.mkOp(Kind::GT);
  Term t16 = tm.mkTerm(o15, {t5, t11});
  Term t17 = tm.mkTerm(Kind::MULT, {t4, t5});
  Term t18 = tm.mkTerm(Kind::GEQ, {t17, t5});
  Op o19 = tm.mkOp(Kind::MULT);
  Term t20 = tm.mkTerm(o19, {t17, t17, t17});
  Op o21 = tm.mkOp(Kind::AND);
  Term t22 = t3.andTerm(t6);
  Term t23 = tm.mkTerm(Kind::GEQ, {t20, t17, t20});
  solver.assertFormula(t6);
  Sort s24 = tm.getBooleanSort();
  Term t25 = tm.mkConst(s0, "_x3");
  Term t26 = tm.mkConst(s0, "_x4");
  Op o27 = tm.mkOp(Kind::LEQ);
  Term t28 = tm.mkTerm(o27, {t17, t26});
  Term t29 = tm.mkTerm(Kind::SUB, {t17, t17});
  Term t30 = tm.mkTerm(Kind::DIVISION, {t17, t17});
  Term t31 = tm.mkTerm(Kind::LEQ, {t17, t17});
  solver.checkSatAssuming({t3, t3, t23, t28, t3});
  solver.blockModel(cvc5::modes::BlockModelsMode::VALUES);
  solver.checkSat();

  return 0;
}
