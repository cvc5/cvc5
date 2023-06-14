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
 * Test for project issue #573
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-models", "true");
  Sort s0 = solver.getRoundingModeSort();
  Sort s1 = solver.mkFloatingPointSort(5, 11);
  Sort s2 = solver.mkBitVectorSort(1);
  Sort s3 = solver.mkBitVectorSort(5);
  Sort s4 = solver.mkBitVectorSort(10);
  Sort s5 = solver.mkBitVectorSort(16);
  Sort s6 = solver.mkFloatingPointSort(11, 53);
  Sort s7 = solver.mkBitVectorSort(1);
  Sort s8 = solver.mkBitVectorSort(11);
  Sort s9 = solver.mkBitVectorSort(52);
  Sort s10 = solver.mkBitVectorSort(64);
  DatatypeDecl d11 = solver.mkDatatypeDecl("_dt0");
  DatatypeConstructorDecl dtcd12 = solver.mkDatatypeConstructorDecl("_cons2");
  dtcd12.addSelector("_sel1", s8);
  d11.addConstructor(dtcd12);
  std::vector<Sort> v13 = solver.mkDatatypeSorts({d11});
  Sort s14 = v13[0];
  Term t15 = solver.mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_ZERO);
  Term t16 = solver.mkVar(s5, "_f3_0");
  Term t17 = solver.mkVar(s8, "_f3_1");
  Term t18 = solver.mkVar(s5, "_f3_2");
  Op o19 = solver.mkOp(EQUAL);
  Term t20 = solver.mkTerm(o19, {t15, t15});
  Sort s21 = t20.getSort();
  Term t22 = solver.mkTerm(DISTINCT, {t20, t20});
  Term t23 = solver.mkTerm(AND, {t22, t22});
  Op o24 = solver.mkOp(SET_SINGLETON);
  Term t25 = solver.mkTerm(o24, {t20});
  Sort s26 = t25.getSort();
  Op o27 = solver.mkOp(SET_CHOOSE);
  Term t28 = solver.mkTerm(o27, {t25});
  Op o29 = solver.mkOp(SET_INSERT);
  Term t30 = solver.mkTerm(o29, {t20, t25});
  Op o31 = solver.mkOp(IMPLIES);
  Term t32 = solver.mkTerm(o31, {t20, t23});
  Op o33 = solver.mkOp(SET_INSERT);
  Term t34 = solver.mkTerm(o29, {t32, t25});
  Term t35 = solver.mkTerm(SET_CHOOSE, {t34});
  Term t36 = solver.mkVar(s14, "_f4_0");
  Term t37 = solver.mkVar(s9, "_f4_1");
  Op o38 = solver.mkOp(SET_CHOOSE);
  Term t39 = solver.mkTerm(o27, {t25});
  Op o40 = solver.mkOp(APPLY_SELECTOR);
  Datatype dt41 = s14.getDatatype();
  DatatypeConstructor dtc42 = dt41.operator[]("_cons2");
  DatatypeSelector dts43 = dtc42.getSelector("_sel1");
  Term t44 = dts43.getTerm();
  Sort s45 = t44.getSort();
  Term t46 = solver.mkTerm(o40, {t44, t36});
  Op o47 = solver.mkOp(APPLY_UPDATER);
  Datatype dt48 = s14.getDatatype();
  DatatypeConstructor dtc49 = dt41.operator[]("_cons2");
  DatatypeSelector dts50 = dtc42.getSelector("_sel1");
  Term t51 = dts43.getUpdaterTerm();
  Sort s52 = t51.getSort();
  Term t53 = solver.mkTerm(o47, {t51, t36, t46});
  Op o54 = solver.mkOp(SET_CHOOSE);
  Term t55 = solver.mkTerm(o27, {t25});
  Op o56 = solver.mkOp(APPLY_UPDATER);
  Datatype dt57 = s14.getDatatype();
  DatatypeConstructor dtc58 = dt41.operator[]("_cons2");
  DatatypeSelector dts59 = dtc42.getSelector("_sel1");
  Term t60 = dts43.getUpdaterTerm();
  Term t61 = solver.mkTerm(o47, {t51, t53, t46});
  Op o62 = solver.mkOp(DISTINCT);
  Term t63 = solver.mkTerm(o62, {t25, t25});
  Term t64 = solver.mkVar(s10, "_f5_0");
  Term t65 = solver.mkVar(s21, "_f5_1");
  Term t66 = solver.mkTerm(SET_CHOOSE, {t25});
  Op o67 = solver.mkOp(ITE);
  Term t68 = t20.iteTerm(t25, t25);
  Op o69 = solver.mkOp(SET_CHOOSE);
  Term t70 = solver.mkTerm(o27, {t25});
  Term t71 = solver.mkTerm(EQUAL, {t25, t25});
  Term t72 = solver.mkVar(s6, "_f6_0");
  Term t73 = solver.mkVar(s9, "_f6_1");
  Op o74 = solver.mkOp(SET_CHOOSE);
  Term t75 = solver.mkTerm(o27, {t25});
  Op o76 = solver.mkOp(FLOATINGPOINT_DIV);
  Term t77 = solver.mkTerm(o76, {t15, t72, t72});
  Op o78 = solver.mkOp(SET_CHOOSE);
  Term t79 = solver.mkTerm(o27, {t25});
  Op o80 = solver.mkOp(FLOATINGPOINT_REM);
  Term t81 = solver.mkTerm(o80, {t77, t72});
  Op o82 = solver.mkOp(ITE);
  Term t83 = solver.mkTerm(o67, {t20, t73, t73});
  Op o84 = solver.mkOp(FLOATINGPOINT_TO_FP_FROM_UBV, {11, 53});
  Term t85 = solver.mkTerm(o84, {t15, t83});
  Op o86 = solver.mkOp(SET_CHOOSE);
  Term t87 = solver.mkTerm(o27, {t25});
  Op o88 = solver.mkOp(FLOATINGPOINT_MIN);
  Term t89 = solver.mkTerm(o88, {t77, t77});
  Op o90 = solver.mkOp(SET_CHOOSE);
  Term t91 = solver.mkTerm(o27, {t25});
  Op o92 = solver.mkOp(SET_CHOOSE);
  Term t93 = solver.mkTerm(o27, {t25});
  Op o94 = solver.mkOp(FLOATINGPOINT_MIN);
  Term t95 = solver.mkTerm(o88, {t77, t77});
  Op o96 = solver.mkOp(SET_CHOOSE);
  Term t97 = solver.mkTerm(o27, {t25});
  Op o98 = solver.mkOp(FLOATINGPOINT_FMA);
  Term t99 = solver.mkTerm(o98, {t15, t77, t77, t77});
  Op o100 = solver.mkOp(ITE);
  Term t101 = solver.mkTerm(o67, {t35, t20, t20});
  Op o102 = solver.mkOp(SET_CHOOSE);
  Term t103 = solver.mkTerm(o27, {t25});
  Op o104 = solver.mkOp(SET_CHOOSE);
  Term t105 = solver.mkTerm(o27, {t25});
  Op o106 = solver.mkOp(FLOATINGPOINT_NEG);
  Term t107 = solver.mkTerm(o106, {t77});
  Op o108 = solver.mkOp(ITE);
  Term t109 = solver.mkTerm(o67, {t101, t101, t20});
  Term t110 = solver.mkVar(s26, "_f7_0");
  Term t111 = solver.mkVar(s4, "_f7_1");
  Term t112 = solver.mkVar(s8, "_f7_2");
  solver.assertFormula(t109);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
