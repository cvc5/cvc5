/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #613
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
  solver.setOption("incremental", "true");
  solver.setOption("produce-models", "true");
  Sort s0 = tm.getRoundingModeSort();
  Sort s1 = tm.mkArraySort(s0, s0);
  Sort s2 = tm.mkSetSort(s1);
  Term t3 = tm.mkUniverseSet(s2);
  Term t4 = tm.mkConst(s1, "_x1");
  Term t5 = tm.mkTerm(Kind::SET_CARD, {t3});
  Sort s6 = t5.getSort();
  Op o7 = tm.mkOp(Kind::BAG_MAKE);
  Term t8 = tm.mkTerm(o7, {t4, t5});
  Sort s9 = t8.getSort();
  solver.checkSat();
  solver.blockModelValues({t8, t4});
  solver.checkSat();

  return 0;
}
