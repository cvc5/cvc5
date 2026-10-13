/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #537
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("quant-ind", "true");
  Sort s0 = tm.getBooleanSort();
  Sort s1 = tm.mkParamSort("_p1");
  Sort s2 = tm.mkParamSort("_p2");
  Sort s3 = tm.mkParamSort("_p3");
  DatatypeDecl d4 = tm.mkDatatypeDecl("_dt0", {s1, s2, s3});
  DatatypeConstructorDecl dtcd5 = tm.mkDatatypeConstructorDecl("_cons9");
  dtcd5.addSelector("_sel8", s2);
  d4.addConstructor(dtcd5);
  Sort s6 = tm.mkParamSort("_p5");
  Sort s7 = tm.mkParamSort("_p6");
  Sort s8 = tm.mkParamSort("_p7");
  DatatypeDecl d9 = tm.mkDatatypeDecl("_dt4", {s6, s7, s8});
  DatatypeConstructorDecl dtcd10 = tm.mkDatatypeConstructorDecl("_cons13");
  dtcd10.addSelector("_sel10", s0);
  dtcd10.addSelector("_sel11", s0);
  dtcd10.addSelector("_sel12", s0);
  d9.addConstructor(dtcd10);
  DatatypeConstructorDecl dtcd11 = tm.mkDatatypeConstructorDecl("_cons16");
  dtcd11.addSelector("_sel14", s7);
  dtcd11.addSelector("_sel15", s6);
  d9.addConstructor(dtcd11);
  DatatypeConstructorDecl dtcd12 = tm.mkDatatypeConstructorDecl("_cons18");
  dtcd12.addSelector("_sel17", s0);
  d9.addConstructor(dtcd12);
  std::vector<Sort> v13 = tm.mkDatatypeSorts({d4, d9});
  Sort s14 = v13[0];
  Sort s15 = v13[1];
  Sort s16 = tm.mkArraySort(s0, s0);
  Sort s17 = s15.instantiate({s0, s16, s16});
  Sort s18 = tm.mkSetSort(s17);
  Term t19 = tm.mkUniverseSet(s18);
  Term t20 = tm.mkTerm(Kind::SET_COMPLEMENT, {t19});
  Op o21 = tm.mkOp(Kind::SET_IS_SINGLETON);
  Term t22 = tm.mkTerm(o21, {t20});
  solver.assertFormula(t22);
  solver.checkSat();

  return 0;
}
