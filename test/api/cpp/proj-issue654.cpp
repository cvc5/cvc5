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
  solver.setOption("produce-interpolants", "true");
  solver.setOption("incremental", "true");
  Sort s0 = solver.getRealSort();
  Term t1 = solver.mkConst(s0, "_x15");
  Term t2 = solver.mkReal(7972974285720917);
  Op o3 = solver.mkOp(Kind::LT);
  Term t4 = solver.mkTerm(o3, {t2, t1});
  Sort s5 = t4.getSort();
  solver.assertFormula(t4);
  Term t6 = solver.getInterpolant(t4);

  return 0;
}
