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
 * Test for project issue #646
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
  solver.setOption("interpolants-mode", "assumptions");
  Sort s0 = tm.getBooleanSort();
  Term t1 = tm.mkConst(s0, "_x1");
  Term t2 = tm.mkBoolean(false);
  solver.assertFormula(t1);
  solver.assertFormula(t1);
  Term t3 = solver.getInterpolant(t2);

  return 0;
}
