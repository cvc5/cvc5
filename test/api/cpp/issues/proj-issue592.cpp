/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #592
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("incremental", "true");
  solver.setOption("produce-models", "true");
  solver.setOption("theoryof-mode", "term");
  Sort s0 = tm.mkUninterpretedSort("_u0");
  Term t1 = tm.mkConst(s0, "_x43");
  Sort s2 = tm.mkSetSort(s0);
  Term t3 = tm.mkConst(s2, "_x111");
  Op o4 = tm.mkOp(Kind::SET_CHOOSE);
  Term t5 = tm.mkTerm(o4, {t3});
  Op o6 = tm.mkOp(Kind::EQUAL);
  Term t7 = t1.eqTerm(t5);
  Sort s8 = t7.getSort();
  solver.checkSat();
  solver.blockModelValues({t7, t5});
  solver.checkSat();

  return 0;
}
