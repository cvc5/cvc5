/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #526
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setLogic("HO_ALL");
  solver.setOption("sets-exp", "true");
  solver.setOption("produce-models", "true");
  Sort s0 = tm.getBooleanSort();
  Sort s1 = tm.mkSetSort(s0);
  Term t2 = tm.mkConst(s1, "_x1");
  Term t3 = tm.mkVar(s0, "_f3_0");
  Op o4 = tm.mkOp(Kind::SET_CHOOSE);
  Term t5 = tm.mkTerm(o4, {t2});
  Sort s6 = tm.mkPredicateSort({s0});
  Term t7 = solver.defineFun("_f3", {t3}, s0, t5);
  Term t8 = tm.mkTerm(Kind::SET_CARD, {t2});
  Sort s9 = t8.getSort();
  solver.checkSat();
  solver.blockModelValues({t7, t2, t2, t8});
  Term t10 = tm.mkTerm(Kind::SET_COMPLEMENT, {t2});
  Term t11 = tm.mkTerm(Kind::SET_SUBSET, {t10, t2});
  solver.checkSat();
  solver.checkSatAssuming({t11, t11, t11, t11, t11});

  return 0;
}
