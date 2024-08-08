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
 * Test for project issue #666
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
  solver.setOption("incremental", "true");
  Sort s0 = tm.getBooleanSort();
  Sort s1 = tm.mkSequenceSort(s0);
  Sort s2 = tm.getRealSort();
  Term t3 = tm.mkConst(s2, "_x35");
  Term t4 = tm.mkVar(s1, "_x37");
  Term t5 = tm.mkConst(s1, "_x38");
  Term t6 = tm.mkReal(5899572550, 9187);
  Term t7 = tm.mkTerm(Kind::DISTINCT, {t3, t6});
  Term t8 = tm.mkTerm(Kind::SEQ_SUFFIX, {t4, t5});
  Term t9 = tm.mkTerm(Kind::SEQ_PREFIX, {t4, t5});
  Op o10 = tm.mkOp(Kind::SEQ_REV);
  Term t11 = tm.mkTerm(o10, {t5});
  Term t12 = tm.mkTerm(Kind::EQUAL, {t9, t8});
  Term t13 = tm.mkTerm(Kind::SET_SINGLETON, {t5});
  Sort s14 = t13.getSort();
  Term t15 = t12.xorTerm(t7);
  Term t16 = tm.mkTerm(Kind::VARIABLE_LIST, {t4});
  Sort s17 = t16.getSort();
  Term t18 = tm.mkTerm(Kind::EXISTS, {t16, t15});
  solver.checkSatAssuming({t18, t18, t7, t7});
  solver.blockModelValues({t11, t13});
  solver.checkSatAssuming({t18, t7, t18, t18, t7});

  return 0;
}
