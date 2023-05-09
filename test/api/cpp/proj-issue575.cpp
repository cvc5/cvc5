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
 * Test for project issue #575
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("preprocess-only", "true");
  solver.setOption("produce-models", "true");
  Sort s0 = solver.mkBitVectorSort(48);
  Sort s1 = solver.getIntegerSort();
  Sort s2 = solver.getRoundingModeSort();
  DatatypeDecl d3 = solver.mkDatatypeDecl("_dt0");
  DatatypeConstructorDecl dtcd4 = solver.mkDatatypeConstructorDecl("_cons5");
  dtcd4.addSelector("_sel1", s0);
  dtcd4.addSelector("_sel2", s1);
  dtcd4.addSelector("_sel3", s1);
  dtcd4.addSelector("_sel4", s1);
  d3.addConstructor(dtcd4);
  DatatypeConstructorDecl dtcd5 = solver.mkDatatypeConstructorDecl("_cons9");
  dtcd5.addSelector("_sel6", s2);
  dtcd5.addSelector("_sel7", s1);
  dtcd5.addSelector("_sel8", s2);
  d3.addConstructor(dtcd5);
  DatatypeConstructorDecl dtcd6 = solver.mkDatatypeConstructorDecl("_cons13");
  dtcd6.addSelector("_sel10", s2);
  dtcd6.addSelector("_sel11", s1);
  dtcd6.addSelector("_sel12", s1);
  d3.addConstructor(dtcd6);
  Sort s7 = solver.declareDatatype("_dt0", {dtcd4, dtcd5, dtcd6});
  DatatypeDecl d8 = solver.mkDatatypeDecl("_dt14");
  DatatypeConstructorDecl dtcd9 = solver.mkDatatypeConstructorDecl("_cons24");
  dtcd9.addSelector("_sel19", s0);
  dtcd9.addSelector("_sel20", s0);
  dtcd9.addSelector("_sel21", s7);
  dtcd9.addSelector("_sel22", s1);
  dtcd9.addSelector("_sel23", s7);
  d8.addConstructor(dtcd9);
  Sort s10 = solver.mkParamSort("_p16");
  Sort s11 = solver.mkParamSort("_p17");
  DatatypeDecl d12 = solver.mkDatatypeDecl("_dt15", {s10, s11});
  DatatypeConstructorDecl dtcd13 = solver.mkDatatypeConstructorDecl("_cons29");
  dtcd13.addSelector("_sel25", s11);
  dtcd13.addSelector("_sel26", s0);
  dtcd13.addSelector("_sel27", s10);
  dtcd13.addSelector("_sel28", s7);
  d12.addConstructor(dtcd13);
  DatatypeConstructorDecl dtcd14 = solver.mkDatatypeConstructorDecl("_cons31");
  dtcd14.addSelector("_sel30", s10);
  d12.addConstructor(dtcd14);
  DatatypeDecl d15 = solver.mkDatatypeDecl("_dt18");
  DatatypeConstructorDecl dtcd16 = solver.mkDatatypeConstructorDecl("_cons34");
  dtcd16.addSelector("_sel32", s0);
  dtcd16.addSelector("_sel33", s1);
  d15.addConstructor(dtcd16);
  DatatypeConstructorDecl dtcd17 = solver.mkDatatypeConstructorDecl("_cons36");
  dtcd17.addSelectorSelf("_sel35");
  d15.addConstructor(dtcd17);
  DatatypeConstructorDecl dtcd18 = solver.mkDatatypeConstructorDecl("_cons37");
  d15.addConstructor(dtcd18);
  DatatypeConstructorDecl dtcd19 = solver.mkDatatypeConstructorDecl("_cons41");
  dtcd19.addSelector("_sel38", s1);
  dtcd19.addSelectorSelf("_sel39");
  dtcd19.addSelector("_sel40", s2);
  d15.addConstructor(dtcd19);
  std::vector<Sort> v20 = solver.mkDatatypeSorts({d8, d12, d15});
  Sort s21 = v20[0];
  Sort s22 = v20[1];
  Sort s23 = v20[2];
  Sort s24 = solver.getRealSort();
  Sort s25 = solver.mkUninterpretedSort("_u42");
  Sort s26 = solver.mkUninterpretedSort("_u43");
  Sort s27 = solver.mkFloatingPointSort(5, 11);
  Sort s28 = solver.mkBitVectorSort(1);
  Sort s29 = solver.mkBitVectorSort(5);
  Sort s30 = solver.mkBitVectorSort(10);
  Sort s31 = solver.mkBitVectorSort(16);
  DatatypeDecl d32 = solver.mkDatatypeDecl("_dt44");
  DatatypeConstructorDecl dtcd33 = solver.mkDatatypeConstructorDecl("_cons45");
  d32.addConstructor(dtcd33);
  DatatypeConstructorDecl dtcd34 = solver.mkDatatypeConstructorDecl("_cons47");
  dtcd34.addSelector("_sel46", s7);
  d32.addConstructor(dtcd34);
  Sort s35 = solver.declareDatatype("_dt44", {dtcd33, dtcd34});
  Sort s36 = solver.mkFunctionSort({s27}, s31);
  Sort s37 = solver.getRoundingModeSort();
  Sort s38 = solver.mkUninterpretedSort("_u48");
  Sort s39 = solver.getRoundingModeSort();
  Term t40 = solver.mkConst(s36, "_x49");
  Term t41 = solver.mkConst(s23, "_x50");
  Term t42 = solver.mkConst(s21, "_x51");
  Term t43 = solver.mkConst(s27, "_x52");
  Term t44 = solver.mkConst(s25, "_x53");
  Term t45 = solver.mkVar(s31, "_x54");
  Term t46 = solver.mkVar(s25, "_x55");
  Term t47 = solver.mkConst(s1, "_x56");
  Term t48 = solver.mkConst(s27, "_x57");
  Term t49 = solver.mkConst(s23, "_x58");
  Term t50 = solver.mkConst(s2, "_x59");
  Term t51 = solver.mkFloatingPointPosZero(5, 11);
  Term t52 = solver.mkConst(s24, "_x61");
  Term t53 = solver.mkBitVector(16, "1011011010000101", 2);
  Term t54 = solver.mkFloatingPoint(5, 11, t53);
  Term t55 = solver.mkVar(s26, "_x62");
  Term t56 = solver.mkTerm(EQUAL, {t52, t52, t52});
  Sort s57 = t56.getSort();
  Op o58 = solver.mkOp(ADD);
  Term t59 = solver.mkTerm(o58, {t47, t47});
  Op o60 = solver.mkOp(NOT);
  Term t61 = solver.mkTerm(o60, {t56});
  Term t62 = solver.mkTerm(APPLY_UF, {t40, t51});
  Term t63 = solver.mkTerm(LT, {t47, t47});
  solver.assertFormula(t61);
  solver.checkSat();
  solver.blockModel(cvc5::modes::BlockModelsMode::LITERALS);

  return 0;
}
