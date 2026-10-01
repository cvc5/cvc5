/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #695
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("incremental", "false");
  solver.setOption("interpolants-mode", "shared");
  solver.setOption("produce-interpolants", "true");
  Sort s0 = tm.mkUninterpretedSort("_u0");
  Sort s1 = tm.getBooleanSort();
  Sort s2 = tm.mkUninterpretedSort("_u11");
  Sort s3 = tm.mkUninterpretedSort("_u12");
  Sort s4 = tm.mkFunctionSort({s2}, s3);
  Term t5 = tm.mkConst(s4, "_x15");
  Sort s6 = tm.mkParamSort("_p27");
  Sort s7 = tm.mkParamSort("_p28");
  Sort s8 = tm.mkParamSort("_p29");
  DatatypeDecl d9 = tm.mkDatatypeDecl("_dt26", {s6, s7, s8});
  DatatypeConstructorDecl dtcd10 = tm.mkDatatypeConstructorDecl("_cons36");
  dtcd10.addSelector("_sel33", s3);
  dtcd10.addSelector("_sel34", s8);
  dtcd10.addSelector("_sel35", s6);
  d9.addConstructor(dtcd10);
  DatatypeConstructorDecl dtcd11 = tm.mkDatatypeConstructorDecl("_cons39");
  dtcd11.addSelector("_sel37", s7);
  dtcd11.addSelector("_sel38", s6);
  d9.addConstructor(dtcd11);
  DatatypeConstructorDecl dtcd12 = tm.mkDatatypeConstructorDecl("_cons45");
  Sort s13 = tm.mkUnresolvedDatatypeSort("_dt30", 2);
  Sort s14 = s13.instantiate({s6, s7});
  dtcd12.addSelector("_sel40", s14);
  dtcd12.addSelector("_sel41", s6);
  dtcd12.addSelector("_sel42", s6);
  dtcd12.addSelector("_sel43", s6);
  dtcd12.addSelector("_sel44", s3);
  d9.addConstructor(dtcd12);
  Sort s15 = tm.mkParamSort("_p31");
  Sort s16 = tm.mkParamSort("_p32");
  DatatypeDecl d17 = tm.mkDatatypeDecl("_dt30", {s15, s16});
  DatatypeConstructorDecl dtcd18 = tm.mkDatatypeConstructorDecl("_cons50");
  dtcd18.addSelector("_sel46", s15);
  dtcd18.addSelector("_sel47", s1);
  dtcd18.addSelector("_sel48", s15);
  dtcd18.addSelector("_sel49", s16);
  d17.addConstructor(dtcd18);
  DatatypeConstructorDecl dtcd19 = tm.mkDatatypeConstructorDecl("_cons54");
  dtcd19.addSelector("_sel51", s16);
  Sort s20 = tm.mkUnresolvedDatatypeSort("_dt26", 3);
  Sort s21 = s20.instantiate({s3, s0, s1});
  dtcd19.addSelector("_sel52", s21);
  Sort s22 = s20.instantiate({s15, s1, s15});
  dtcd19.addSelector("_sel53", s22);
  d17.addConstructor(dtcd19);
  std::vector<Sort> v23 = tm.mkDatatypeSorts({d9, d17});
  Sort s24 = v23[0];
  Sort s25 = v23[1];
  Sort s26 = s24.instantiate({s3, s0, s1});
  Sort s27 = s25.instantiate({s3, s0});
  Sort s28 = s24.instantiate({s3, s1, s3});
  Sort s29 = s25.instantiate({s3, s1});
  Sort s30 = s24.instantiate({s3, s0, s1});
  Sort s31 = s25.instantiate({s3, s0});
  Sort s32 = s24.instantiate({s3, s1, s3});
  Sort s33 = s25.instantiate({s3, s1});
  Sort s34 = s25.instantiate({s3, s0});
  Sort s35 = s24.instantiate({s3, s1, s3});
  Sort s36 = s25.instantiate({s3, s1});
  Sort s37 = s25.instantiate({s3, s1});
  Sort s38 = s24.instantiate({s3, s1, s3});
  Sort s39 = s24.instantiate({s3, s1, s3});
  Sort s40 = s25.instantiate({s3, s1});
  Term t41 = tm.mkConst(s2, "_x55");
  Term t42 = tm.mkConst(s26, "_x56");
  Term t43 = tm.mkConst(s1, "_x57");
  Sort s44 = tm.mkUninterpretedSort("_u64");
  Sort s45 = tm.mkParamSort("_p67");
  DatatypeDecl d46 = tm.mkDatatypeDecl("_dt66", {s45});
  DatatypeConstructorDecl dtcd47 = tm.mkDatatypeConstructorDecl("_cons70");
  d46.addConstructor(dtcd47);
  DatatypeDecl d48 = tm.mkDatatypeDecl("_dt68");
  DatatypeConstructorDecl dtcd49 = tm.mkDatatypeConstructorDecl("_cons75");
  dtcd49.addSelector("_sel71", s26);
  dtcd49.addSelector("_sel72", s44);
  dtcd49.addSelector("_sel73", s26);
  dtcd49.addSelector("_sel74", s1);
  d48.addConstructor(dtcd49);
  DatatypeConstructorDecl dtcd50 = tm.mkDatatypeConstructorDecl("_cons79");
  dtcd50.addSelectorSelf("_sel76");
  dtcd50.addSelector("_sel77", s2);
  dtcd50.addSelector("_sel78", s44);
  d48.addConstructor(dtcd50);
  DatatypeConstructorDecl dtcd51 = tm.mkDatatypeConstructorDecl("_cons82");
  dtcd51.addSelector("_sel80", s0);
  dtcd51.addSelector("_sel81", s2);
  d48.addConstructor(dtcd51);
  DatatypeDecl d52 = tm.mkDatatypeDecl("_dt69");
  DatatypeConstructorDecl dtcd53 = tm.mkDatatypeConstructorDecl("_cons85");
  dtcd53.addSelector("_sel83", s28);
  dtcd53.addSelector("_sel84", s26);
  d52.addConstructor(dtcd53);
  DatatypeConstructorDecl dtcd54 = tm.mkDatatypeConstructorDecl("_cons89");
  dtcd54.addSelector("_sel86", s27);
  dtcd54.addSelectorSelf("_sel87");
  dtcd54.addSelector("_sel88", s29);
  d52.addConstructor(dtcd54);
  std::vector<Sort> v55 = tm.mkDatatypeSorts({d46, d48, d52});
  Sort s56 = v55[0];
  Sort s57 = v55[1];
  Sort s58 = v55[2];
  DatatypeDecl d59 = tm.mkDatatypeDecl("_dt125");
  DatatypeConstructorDecl dtcd60 = tm.mkDatatypeConstructorDecl("_cons126");
  d59.addConstructor(dtcd60);
  DatatypeConstructorDecl dtcd61 = tm.mkDatatypeConstructorDecl("_cons129");
  dtcd61.addSelector("_sel127", s28);
  dtcd61.addSelector("_sel128", s0);
  d59.addConstructor(dtcd61);
  DatatypeConstructorDecl dtcd62 = tm.mkDatatypeConstructorDecl("_cons133");
  dtcd62.addSelector("_sel130", s0);
  dtcd62.addSelector("_sel131", s44);
  dtcd62.addSelector("_sel132", s57);
  d59.addConstructor(dtcd62);
  std::vector<Sort> v63 = tm.mkDatatypeSorts({d59});
  Sort s64 = v63[0];
  Sort s65 = s25.instantiate({s26, s27});
  Sort s66 = s24.instantiate({s26, s1, s26});
  Sort s67 = s25.instantiate({s26, s1});
  Sort s68 = s25.instantiate({s26, s1});
  Sort s69 = s24.instantiate({s26, s1, s26});
  Term t70 = tm.mkConst(s65, "_x135");
  Term t71 = tm.mkTerm(Kind::APPLY_UF, {t5, t41});
  Datatype dt72 = s26.getDatatype();
  DatatypeConstructor dtc73 = dt72.getConstructor("_cons45");
  DatatypeSelector dts74 = dtc73.operator[]("_sel43");
  Term t75 = dts74.getUpdaterTerm();
  Sort s76 = t75.getSort();
  Term t77 = tm.mkTerm(Kind::APPLY_UPDATER, {t75, t42, t71});
  Op o78 = tm.mkOp(Kind::APPLY_SELECTOR);
  Datatype dt79 = s65.getDatatype();
  DatatypeConstructor dtc80 = dt79.operator[]("_cons54");
  DatatypeSelector dts81 = dtc80.getSelector("_sel53");
  Term t82 = dts81.getTerm();
  Sort s83 = t82.getSort();
  Term t84 = tm.mkTerm(o78, {t82, t70});
  Datatype dt85 = s66.getDatatype();
  DatatypeConstructor dtc86 = dt72.getConstructor("_cons39");
  Term t87 = dtc86.getInstantiatedTerm(s66);
  Sort s88 = t87.getSort();
  Term t89 = tm.mkTerm(Kind::APPLY_CONSTRUCTOR, {t87, t43, t77});
  Term t90 = tm.mkTerm(Kind::ITE, {t43, t89, t84});
  Datatype dt91 = s66.getDatatype();
  DatatypeConstructor dtc92 = dt72.getConstructor("_cons39");
  DatatypeSelector dts93 = dtc86.operator[]("_sel37");
  Term t94 = dts93.getTerm();
  Sort s95 = t94.getSort();
  Term t96 = tm.mkTerm(Kind::APPLY_SELECTOR, {t94, t90});
  Term t97 = tm.mkVar(s67, "_f220_0");
  Term t98 = tm.mkVar(s64, "_f220_1");
  Term t99 = tm.mkTerm(Kind::ITE, {t96, t97, t97});
  Sort s100 = tm.mkFunctionSort({s67, s64}, s67);
  Term t101 = solver.defineFun("_f220", {t97, t98}, s67, t99, true);
  Term t102 = solver.getInterpolant(t96);

  return 0;
}
