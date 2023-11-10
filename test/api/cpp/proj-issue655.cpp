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
 * Test for project issue #655
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-abducts", "true");
  Sort s0 = solver.getBooleanSort();
  DatatypeDecl d1 = solver.mkDatatypeDecl("_dt0");
  DatatypeConstructorDecl dtcd2 = solver.mkDatatypeConstructorDecl("_cons7");
  dtcd2.addSelectorSelf("_sel4");
  dtcd2.addSelector("_sel5", s0);
  dtcd2.addSelector("_sel6", s0);
  d1.addConstructor(dtcd2);
  DatatypeConstructorDecl dtcd3 = solver.mkDatatypeConstructorDecl("_cons12");
  dtcd3.addSelectorSelf("_sel8");
  dtcd3.addSelector("_sel9", s0);
  dtcd3.addSelector("_sel10", s0);
  dtcd3.addSelector("_sel11", s0);
  d1.addConstructor(dtcd3);
  DatatypeConstructorDecl dtcd4 = solver.mkDatatypeConstructorDecl("_cons17");
  dtcd4.addSelector("_sel13", s0);
  dtcd4.addSelector("_sel14", s0);
  dtcd4.addSelector("_sel15", s0);
  dtcd4.addSelector("_sel16", s0);
  d1.addConstructor(dtcd4);
  DatatypeDecl d5 = solver.mkDatatypeDecl("_dt1");
  DatatypeConstructorDecl dtcd6 = solver.mkDatatypeConstructorDecl("_cons19");
  dtcd6.addSelectorSelf("_sel18");
  d5.addConstructor(dtcd6);
  DatatypeConstructorDecl dtcd7 = solver.mkDatatypeConstructorDecl("_cons21");
  dtcd7.addSelector("_sel20", s0);
  d5.addConstructor(dtcd7);
  DatatypeConstructorDecl dtcd8 = solver.mkDatatypeConstructorDecl("_cons22");
  d5.addConstructor(dtcd8);
  Sort s9 = solver.mkParamSort("_p3");
  DatatypeDecl d10 = solver.mkDatatypeDecl("_dt2", {s9});
  DatatypeConstructorDecl dtcd11 = solver.mkDatatypeConstructorDecl("_cons27");
  dtcd11.addSelector("_sel23", s9);
  dtcd11.addSelector("_sel24", s0);
  dtcd11.addSelector("_sel25", s0);
  dtcd11.addSelector("_sel26", s9);
  d10.addConstructor(dtcd11);
  DatatypeConstructorDecl dtcd12 = solver.mkDatatypeConstructorDecl("_cons30");
  dtcd12.addSelector("_sel28", s9);
  dtcd12.addSelector("_sel29", s0);
  d10.addConstructor(dtcd12);
  DatatypeConstructorDecl dtcd13 = solver.mkDatatypeConstructorDecl("_cons33");
  dtcd13.addSelectorSelf("_sel31");
  dtcd13.addSelector("_sel32", s0);
  d10.addConstructor(dtcd13);
  DatatypeConstructorDecl dtcd14 = solver.mkDatatypeConstructorDecl("_cons36");
  dtcd14.addSelector("_sel34", s0);
  dtcd14.addSelectorSelf("_sel35");
  d10.addConstructor(dtcd14);
  std::vector<Sort> v15 = solver.mkDatatypeSorts({d1, d5, d10});
  Sort s16 = v15[0];
  Sort s17 = v15[1];
  Sort s18 = v15[2];
  Term t19 = solver.mkConst(s16, "_x66");
  Datatype dt20 = s16.getDatatype();
  DatatypeConstructor dtc21 = dt20.operator[]("_cons17");
  Term t22 = dtc21.getTesterTerm();
  Sort s23 = t22.getSort();
  Term t24 = solver.mkTerm(Kind::APPLY_TESTER, {t22, t19});
  Term t25 = solver.getAbduct(t24);

  return 0;
}
