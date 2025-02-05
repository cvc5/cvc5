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
 * Test for project issue #575
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("preprocess-only", "true");
  solver.setOption("produce-models", "true");
  Sort s0 = tm.mkBitVectorSort(48);
  Sort s1 = tm.getIntegerSort();
  Sort s2 = tm.getRoundingModeSort();
  DatatypeDecl d3 = tm.mkDatatypeDecl("_dt0");
  DatatypeConstructorDecl dtcd4 = tm.mkDatatypeConstructorDecl("_cons5");
  dtcd4.addSelector("_sel1", s0);
  dtcd4.addSelector("_sel2", s1);
  dtcd4.addSelector("_sel3", s1);
  dtcd4.addSelector("_sel4", s1);
  d3.addConstructor(dtcd4);
  DatatypeConstructorDecl dtcd5 = tm.mkDatatypeConstructorDecl("_cons9");
  dtcd5.addSelector("_sel6", s2);
  dtcd5.addSelector("_sel7", s1);
  dtcd5.addSelector("_sel8", s2);
  d3.addConstructor(dtcd5);
  DatatypeConstructorDecl dtcd6 = tm.mkDatatypeConstructorDecl("_cons13");
  dtcd6.addSelector("_sel10", s2);
  dtcd6.addSelector("_sel11", s1);
  dtcd6.addSelector("_sel12", s1);
  d3.addConstructor(dtcd6);
  Sort s7 = solver.declareDatatype("_dt0", {dtcd4, dtcd5, dtcd6});
  DatatypeDecl d8 = tm.mkDatatypeDecl("_dt14");
  DatatypeConstructorDecl dtcd9 = tm.mkDatatypeConstructorDecl("_cons24");
  dtcd9.addSelector("_sel19", s0);
  dtcd9.addSelector("_sel20", s0);
  dtcd9.addSelector("_sel21", s7);
  dtcd9.addSelector("_sel22", s1);
  dtcd9.addSelector("_sel23", s7);
  d8.addConstructor(dtcd9);
  Sort s10 = tm.mkParamSort("_p16");
  Sort s11 = tm.mkParamSort("_p17");
  DatatypeDecl d12 = tm.mkDatatypeDecl("_dt15", {s10, s11});
  DatatypeConstructorDecl dtcd13 = tm.mkDatatypeConstructorDecl("_cons29");
  dtcd13.addSelector("_sel25", s11);
  dtcd13.addSelector("_sel26", s0);
  dtcd13.addSelector("_sel27", s10);
  dtcd13.addSelector("_sel28", s7);
  d12.addConstructor(dtcd13);
  DatatypeConstructorDecl dtcd14 = tm.mkDatatypeConstructorDecl("_cons31");
  dtcd14.addSelector("_sel30", s10);
  d12.addConstructor(dtcd14);
  DatatypeDecl d15 = tm.mkDatatypeDecl("_dt18");
  DatatypeConstructorDecl dtcd16 = tm.mkDatatypeConstructorDecl("_cons34");
  dtcd16.addSelector("_sel32", s0);
  dtcd16.addSelector("_sel33", s1);
  d15.addConstructor(dtcd16);
  DatatypeConstructorDecl dtcd17 = tm.mkDatatypeConstructorDecl("_cons36");
  dtcd17.addSelectorSelf("_sel35");
  d15.addConstructor(dtcd17);
  DatatypeConstructorDecl dtcd18 = tm.mkDatatypeConstructorDecl("_cons37");
  d15.addConstructor(dtcd18);
  DatatypeConstructorDecl dtcd19 = tm.mkDatatypeConstructorDecl("_cons41");
  dtcd19.addSelector("_sel38", s1);
  dtcd19.addSelectorSelf("_sel39");
  dtcd19.addSelector("_sel40", s2);
  d15.addConstructor(dtcd19);
  std::vector<Sort> v20 = tm.mkDatatypeSorts({d8, d12, d15});
  Sort s21 = v20[0];
  Sort s22 = v20[1];
  Sort s23 = v20[2];
  Sort s24 = tm.getRealSort();
  Sort s25 = tm.mkUninterpretedSort("_u42");
  Sort s26 = tm.mkUninterpretedSort("_u43");
  Sort s27 = tm.mkFloatingPointSort(5, 11);
  Sort s28 = tm.mkBitVectorSort(1);
  Sort s29 = tm.mkBitVectorSort(5);
  Sort s30 = tm.mkBitVectorSort(10);
  Sort s31 = tm.mkBitVectorSort(16);
  DatatypeDecl d32 = tm.mkDatatypeDecl("_dt44");
  DatatypeConstructorDecl dtcd33 = tm.mkDatatypeConstructorDecl("_cons45");
  d32.addConstructor(dtcd33);
  DatatypeConstructorDecl dtcd34 = tm.mkDatatypeConstructorDecl("_cons47");
  dtcd34.addSelector("_sel46", s7);
  d32.addConstructor(dtcd34);
  Sort s35 = solver.declareDatatype("_dt44", {dtcd33, dtcd34});
  Sort s36 = tm.mkFunctionSort({s27}, s31);
  Sort s37 = tm.getRoundingModeSort();
  Sort s38 = tm.mkUninterpretedSort("_u48");
  Sort s39 = tm.getRoundingModeSort();
  Term t40 = tm.mkConst(s36, "_x49");
  Term t41 = tm.mkConst(s23, "_x50");
  Term t42 = tm.mkConst(s21, "_x51");
  Term t43 = tm.mkConst(s27, "_x52");
  Term t44 = tm.mkConst(s25, "_x53");
  Term t45 = tm.mkVar(s31, "_x54");
  Term t46 = tm.mkVar(s25, "_x55");
  Term t47 = tm.mkConst(s1, "_x56");
  Term t48 = tm.mkConst(s27, "_x57");
  Term t49 = tm.mkConst(s23, "_x58");
  Term t50 = tm.mkConst(s2, "_x59");
  Term t51 = tm.mkFloatingPointPosZero(5, 11);
  Term t52 = tm.mkConst(s24, "_x61");
  Term t53 = tm.mkBitVector(16, "1011011010000101", 2);
  Term t54 = tm.mkFloatingPoint(5, 11, t53);
  Term t55 = tm.mkVar(s26, "_x62");
  Term t56 = tm.mkTerm(Kind::EQUAL, {t52, t52, t52});
  Sort s57 = t56.getSort();
  Op o58 = tm.mkOp(Kind::ADD);
  Term t59 = tm.mkTerm(o58, {t47, t47});
  Op o60 = tm.mkOp(Kind::NOT);
  Term t61 = tm.mkTerm(o60, {t56});
  Term t62 = tm.mkTerm(Kind::APPLY_UF, {t40, t51});
  Term t63 = tm.mkTerm(Kind::LT, {t47, t47});
  solver.assertFormula(t61);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
