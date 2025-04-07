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
 * Test for project issue #587
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("produce-interpolants", "true");
  solver.setOption("incremental", "true");
  Sort s0 = tm.getRealSort();
  Term t1 = tm.mkConst(s0, "_x15");
  Term t2 = tm.mkReal(7972974285720917);
  Op o3 = tm.mkOp(Kind::LT);
  Term t4 = tm.mkTerm(o3, {t2, t1});
  Sort s5 = t4.getSort();
  solver.assertFormula(t4);
  Term t6 = solver.getInterpolant(t4);

  return 0;
}
