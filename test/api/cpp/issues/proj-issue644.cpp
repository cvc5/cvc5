/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #644
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
  solver.setOption("check-interpolants", "true");
  solver.setOption("produce-interpolants", "true");
  Sort s0 = tm.getRoundingModeSort();
  Term t1 = tm.mkConst(s0, "_x0");
  Term t2 = tm.mkTerm(Kind::SET_SINGLETON, {t1});
  Sort s3 = t2.getSort();
  Op o4 = tm.mkOp(Kind::SET_COMPLEMENT);
  Term t5 = tm.mkTerm(o4, {t2});
  Term t6 = tm.mkTerm(Kind::SET_COMPLEMENT, {t5});
  Op o7 = tm.mkOp(Kind::SET_SUBSET);
  Term t8 = tm.mkTerm(o7, {t6, t5});
  Sort s9 = t8.getSort();
  solver.assertFormula(t8);
  Term t10 = solver.getInterpolant(t8);

  return 0;
}
