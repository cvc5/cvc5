/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #581
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("sets-exp", "true");
  solver.setOption("produce-interpolants", "true");
  DatatypeDecl d0 = tm.mkDatatypeDecl("_dt0");
  DatatypeConstructorDecl dtcd1 = tm.mkDatatypeConstructorDecl("_cons8");
  d0.addConstructor(dtcd1);
  Sort s2 = tm.mkParamSort("_p2");
  Sort s3 = tm.mkParamSort("_p3");
  DatatypeDecl d4 = tm.mkDatatypeDecl("_dt1", {s2, s3});
  DatatypeConstructorDecl dtcd5 = tm.mkDatatypeConstructorDecl("_cons14");
  Sort s6 = tm.mkUnresolvedDatatypeSort("_dt4", 3);
  Sort s7 = s6.instantiate({s2, s2, s2});
  dtcd5.addSelector("_sel9", s7);
  dtcd5.addSelectorSelf("_sel10");
  dtcd5.addSelectorSelf("_sel11");
  Sort s8 = tm.mkUnresolvedDatatypeSort("_dt0", 0);
  dtcd5.addSelector("_sel12", s8);
  dtcd5.addSelectorSelf("_sel13");
  d4.addConstructor(dtcd5);
  DatatypeConstructorDecl dtcd9 = tm.mkDatatypeConstructorDecl("_cons19");
  dtcd9.addSelector("_sel15", s2);
  dtcd9.addSelectorSelf("_sel16");
  dtcd9.addSelector("_sel17", s8);
  dtcd9.addSelector("_sel18", s8);
  d4.addConstructor(dtcd9);
  DatatypeConstructorDecl dtcd10 = tm.mkDatatypeConstructorDecl("_cons25");
  dtcd10.addSelector("_sel20", s3);
  dtcd10.addSelector("_sel21", s3);
  dtcd10.addSelector("_sel22", s3);
  dtcd10.addSelector("_sel23", s3);
  dtcd10.addSelector("_sel24", s3);
  d4.addConstructor(dtcd10);
  DatatypeConstructorDecl dtcd11 = tm.mkDatatypeConstructorDecl("_cons31");
  dtcd11.addSelector("_sel26", s2);
  Sort s12 = s6.instantiate({s3, s2, s2});
  dtcd11.addSelector("_sel27", s12);
  Sort s13 = s6.instantiate({s3, s2, s3});
  dtcd11.addSelector("_sel28", s13);
  dtcd11.addSelector("_sel29", s2);
  dtcd11.addSelector("_sel30", s3);
  d4.addConstructor(dtcd11);
  Sort s14 = tm.mkParamSort("_p5");
  Sort s15 = tm.mkParamSort("_p6");
  Sort s16 = tm.mkParamSort("_p7");
  DatatypeDecl d17 = tm.mkDatatypeDecl("_dt4", {s14, s15, s16});
  DatatypeConstructorDecl dtcd18 = tm.mkDatatypeConstructorDecl("_cons32");
  d17.addConstructor(dtcd18);
  DatatypeConstructorDecl dtcd19 = tm.mkDatatypeConstructorDecl("_cons35");
  Sort s20 = tm.mkUnresolvedDatatypeSort("_dt0", 0);
  dtcd19.addSelector("_sel33", s20);
  dtcd19.addSelectorSelf("_sel34");
  d17.addConstructor(dtcd19);
  DatatypeConstructorDecl dtcd21 = tm.mkDatatypeConstructorDecl("_cons39");
  dtcd21.addSelectorSelf("_sel36");
  Sort s22 = tm.mkUnresolvedDatatypeSort("_dt1", 2);
  Sort s23 = s22.instantiate({s16, s16});
  dtcd21.addSelector("_sel37", s23);
  dtcd21.addSelector("_sel38", s15);
  d17.addConstructor(dtcd21);
  DatatypeConstructorDecl dtcd24 = tm.mkDatatypeConstructorDecl("_cons44");
  dtcd24.addSelectorSelf("_sel40");
  dtcd24.addSelector("_sel41", s15);
  dtcd24.addSelector("_sel42", s20);
  dtcd24.addSelector("_sel43", s16);
  d17.addConstructor(dtcd24);
  std::vector<Sort> v25 = tm.mkDatatypeSorts({d0, d4, d17});
  Sort s26 = v25[0];
  Sort s27 = v25[1];
  Sort s28 = v25[2];
  Sort s29 = tm.mkSetSort(s26);
  Term t30 = tm.mkConst(s29, "_x46");
  Term t31 = tm.mkUniverseSet(s29);
  Term t32 = tm.mkVar(s29, "_f49_0");
  Term t33 = tm.mkVar(s29, "_f49_1");
  Term t34 = tm.mkVar(s29, "_f49_2");
  Term t35 = tm.mkTerm(Kind::SET_CHOOSE, {t34});
  Term t36 = tm.mkTerm(Kind::SET_INSERT, {t35, t30});
  Sort s37 = tm.mkFunctionSort({s29, s29, s29}, s29);
  Term t38 = solver.defineFun("_f49", {t32, t33, t34}, s29, t36, true);
  Term t39 = tm.mkTerm(Kind::APPLY_UF, {t38, t30, t30, t30});
  Op o40 = tm.mkOp(Kind::SET_MINUS);
  Term t41 = tm.mkTerm(o40, {t30, t30});
  Op o42 = tm.mkOp(Kind::SET_IS_SINGLETON);
  Term t43 = tm.mkTerm(o42, {t31});
  Sort s44 = t43.getSort();
  Op o45 = tm.mkOp(Kind::EQUAL);
  Term t46 = t39.eqTerm(t41);
  Term t47 = t46.xorTerm(t43);
  solver.assertFormula(t43);
  Term t48 = solver.getInterpolant(t47);

  return 0;
}
