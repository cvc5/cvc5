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
 * Test for project issue #573
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
  Sort s0 = tm.getRoundingModeSort();
  Sort s1 = tm.mkFloatingPointSort(5, 11);
  Sort s2 = tm.mkBitVectorSort(1);
  Sort s3 = tm.mkBitVectorSort(5);
  Sort s4 = tm.mkBitVectorSort(10);
  Sort s5 = tm.mkBitVectorSort(16);
  Sort s6 = tm.mkFloatingPointSort(11, 53);
  Sort s7 = tm.mkBitVectorSort(1);
  Sort s8 = tm.mkBitVectorSort(11);
  Sort s9 = tm.mkBitVectorSort(52);
  Sort s10 = tm.mkBitVectorSort(64);
  DatatypeDecl d11 = tm.mkDatatypeDecl("_dt0");
  DatatypeConstructorDecl dtcd12 = tm.mkDatatypeConstructorDecl("_cons2");
  dtcd12.addSelector("_sel1", s8);
  d11.addConstructor(dtcd12);
  std::vector<Sort> v13 = tm.mkDatatypeSorts({d11});
  Sort s14 = v13[0];
  Term t15 = tm.mkRoundingMode(cvc5::RoundingMode::ROUND_TOWARD_ZERO);
  Term t16 = tm.mkVar(s5, "_f3_0");
  Term t17 = tm.mkVar(s8, "_f3_1");
  Term t18 = tm.mkVar(s5, "_f3_2");
  Op o19 = tm.mkOp(Kind::EQUAL);
  Term t20 = tm.mkTerm(o19, {t15, t15});
  Sort s21 = t20.getSort();
  Term t22 = tm.mkTerm(Kind::DISTINCT, {t20, t20});
  Term t23 = tm.mkTerm(Kind::AND, {t22, t22});
  Op o24 = tm.mkOp(Kind::SET_SINGLETON);
  Term t25 = tm.mkTerm(o24, {t20});
  Sort s26 = t25.getSort();
  Op o27 = tm.mkOp(Kind::SET_CHOOSE);
  Term t28 = tm.mkTerm(o27, {t25});
  Op o29 = tm.mkOp(Kind::SET_INSERT);
  Term t30 = tm.mkTerm(o29, {t20, t25});
  Op o31 = tm.mkOp(Kind::IMPLIES);
  Term t32 = tm.mkTerm(o31, {t20, t23});
  Op o33 = tm.mkOp(Kind::SET_INSERT);
  Term t34 = tm.mkTerm(o29, {t32, t25});
  Term t35 = tm.mkTerm(Kind::SET_CHOOSE, {t34});
  Term t36 = tm.mkVar(s14, "_f4_0");
  Term t37 = tm.mkVar(s9, "_f4_1");
  Op o38 = tm.mkOp(Kind::SET_CHOOSE);
  Term t39 = tm.mkTerm(o27, {t25});
  Op o40 = tm.mkOp(Kind::APPLY_SELECTOR);
  Datatype dt41 = s14.getDatatype();
  DatatypeConstructor dtc42 = dt41.operator[]("_cons2");
  DatatypeSelector dts43 = dtc42.getSelector("_sel1");
  Term t44 = dts43.getTerm();
  Sort s45 = t44.getSort();
  Term t46 = tm.mkTerm(o40, {t44, t36});
  Op o47 = tm.mkOp(Kind::APPLY_UPDATER);
  Datatype dt48 = s14.getDatatype();
  DatatypeConstructor dtc49 = dt41.operator[]("_cons2");
  DatatypeSelector dts50 = dtc42.getSelector("_sel1");
  Term t51 = dts43.getUpdaterTerm();
  Sort s52 = t51.getSort();
  Term t53 = tm.mkTerm(o47, {t51, t36, t46});
  Op o54 = tm.mkOp(Kind::SET_CHOOSE);
  Term t55 = tm.mkTerm(o27, {t25});
  Op o56 = tm.mkOp(Kind::APPLY_UPDATER);
  Datatype dt57 = s14.getDatatype();
  DatatypeConstructor dtc58 = dt41.operator[]("_cons2");
  DatatypeSelector dts59 = dtc42.getSelector("_sel1");
  Term t60 = dts43.getUpdaterTerm();
  Term t61 = tm.mkTerm(o47, {t51, t53, t46});
  Op o62 = tm.mkOp(Kind::DISTINCT);
  Term t63 = tm.mkTerm(o62, {t25, t25});
  Term t64 = tm.mkVar(s10, "_f5_0");
  Term t65 = tm.mkVar(s21, "_f5_1");
  Term t66 = tm.mkTerm(Kind::SET_CHOOSE, {t25});
  Op o67 = tm.mkOp(Kind::ITE);
  Term t68 = t20.iteTerm(t25, t25);
  Op o69 = tm.mkOp(Kind::SET_CHOOSE);
  Term t70 = tm.mkTerm(o27, {t25});
  Term t71 = tm.mkTerm(Kind::EQUAL, {t25, t25});
  Term t72 = tm.mkVar(s6, "_f6_0");
  Term t73 = tm.mkVar(s9, "_f6_1");
  Op o74 = tm.mkOp(Kind::SET_CHOOSE);
  Term t75 = tm.mkTerm(o27, {t25});
  Op o76 = tm.mkOp(Kind::FLOATINGPOINT_DIV);
  Term t77 = tm.mkTerm(o76, {t15, t72, t72});
  Op o78 = tm.mkOp(Kind::SET_CHOOSE);
  Term t79 = tm.mkTerm(o27, {t25});
  Op o80 = tm.mkOp(Kind::FLOATINGPOINT_REM);
  Term t81 = tm.mkTerm(o80, {t77, t72});
  Op o82 = tm.mkOp(Kind::ITE);
  Term t83 = tm.mkTerm(o67, {t20, t73, t73});
  Op o84 = tm.mkOp(Kind::FLOATINGPOINT_TO_FP_FROM_UBV, {11, 53});
  Term t85 = tm.mkTerm(o84, {t15, t83});
  Op o86 = tm.mkOp(Kind::SET_CHOOSE);
  Term t87 = tm.mkTerm(o27, {t25});
  Op o88 = tm.mkOp(Kind::FLOATINGPOINT_MIN);
  Term t89 = tm.mkTerm(o88, {t77, t77});
  Op o90 = tm.mkOp(Kind::SET_CHOOSE);
  Term t91 = tm.mkTerm(o27, {t25});
  Op o92 = tm.mkOp(Kind::SET_CHOOSE);
  Term t93 = tm.mkTerm(o27, {t25});
  Op o94 = tm.mkOp(Kind::FLOATINGPOINT_MIN);
  Term t95 = tm.mkTerm(o88, {t77, t77});
  Op o96 = tm.mkOp(Kind::SET_CHOOSE);
  Term t97 = tm.mkTerm(o27, {t25});
  Op o98 = tm.mkOp(Kind::FLOATINGPOINT_FMA);
  Term t99 = tm.mkTerm(o98, {t15, t77, t77, t77});
  Op o100 = tm.mkOp(Kind::ITE);
  Term t101 = tm.mkTerm(o67, {t35, t20, t20});
  Op o102 = tm.mkOp(Kind::SET_CHOOSE);
  Term t103 = tm.mkTerm(o27, {t25});
  Op o104 = tm.mkOp(Kind::SET_CHOOSE);
  Term t105 = tm.mkTerm(o27, {t25});
  Op o106 = tm.mkOp(Kind::FLOATINGPOINT_NEG);
  Term t107 = tm.mkTerm(o106, {t77});
  Op o108 = tm.mkOp(Kind::ITE);
  Term t109 = tm.mkTerm(o67, {t101, t101, t20});
  Term t110 = tm.mkVar(s26, "_f7_0");
  Term t111 = tm.mkVar(s4, "_f7_1");
  Term t112 = tm.mkVar(s8, "_f7_2");
  solver.assertFormula(t109);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
