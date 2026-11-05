/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #588
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
  solver.setOption("sygus-core-connective", "true");
  solver.setOption("produce-interpolants", "true");
  Sort s0 = tm.getBooleanSort();
  Term t1 = tm.mkConst(s0, "_x1");
  Term t2 = tm.mkVar(s0, "_f3_0");
  Term t3 = tm.mkVar(s0, "_f3_1");
  Sort s4 = tm.mkFunctionSort({s0, s0}, s0);
  Term t5 = solver.defineFun("_f3", {t2, t3}, s0, t1, true);
  Term t6 = solver.getInterpolant(t1);

  return 0;
}
