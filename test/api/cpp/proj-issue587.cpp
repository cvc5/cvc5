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
 * Test for project issue #587
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("sygus-core-connective", "true");
  solver.setOption("produce-abducts", "true");
  Sort s0 = solver.getBooleanSort();
  Sort s1 = solver.mkSetSort(s0);
  Sort s2 = solver.mkSetSort(s1);
  Term t3 = solver.mkEmptySet(s2);
  Term t4 = solver.mkConst(s1, "_x2");
  Op o5 = solver.mkOp(SET_SINGLETON);
  Term t6 = solver.mkTerm(o5, {t3});
  Sort s7 = t6.getSort();
  Op o8 = solver.mkOp(SET_SINGLETON);
  Term t9 = solver.mkTerm(o5, {t6});
  Sort s10 = t9.getSort();
  Op o11 = solver.mkOp(SET_MINUS);
  Term t12 = solver.mkTerm(o11, {t9, t9});
  Op o13 = solver.mkOp(SET_IS_SINGLETON);
  Term t14 = solver.mkTerm(o13, {t12});
  solver.assertFormula(t14);
  Op o15 = solver.mkOp(SET_MEMBER);
  Term t16 = solver.mkTerm(o15, {t14, t4});
  Term t17 = solver.getAbduct(t16);

  return 0;
}
