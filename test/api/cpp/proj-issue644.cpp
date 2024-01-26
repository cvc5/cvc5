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
 * Test for project issue #644
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("sets-ext", "true");
  solver.setOption("check-interpolants", "true");
  solver.setOption("produce-interpolants", "true");
  Sort s0 = solver.getRoundingModeSort();
  Term t1 = solver.mkConst(s0, "_x0");
  Term t2 = solver.mkTerm(Kind::SET_SINGLETON, {t1});
  Sort s3 = t2.getSort();
  Op o4 = solver.mkOp(Kind::SET_COMPLEMENT);
  Term t5 = solver.mkTerm(o4, {t2});
  Term t6 = solver.mkTerm(Kind::SET_COMPLEMENT, {t5});
  Op o7 = solver.mkOp(Kind::SET_SUBSET);
  Term t8 = solver.mkTerm(o7, {t6, t5});
  Sort s9 = t8.getSort();
  solver.assertFormula(t8);
  Term t10 = solver.getInterpolant(t8);

  return 0;
}
