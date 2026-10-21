/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #565
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
  solver.setOption("interpolants-mode", "all");
  Op o0 = tm.mkOp(Kind::PI);
  Term t1 = tm.mkTerm(o0);
  Sort s2 = t1.getSort();
  Term t3 = tm.mkTerm(Kind::DISTINCT, {t1, t1});
  Sort s4 = t3.getSort();
  solver.assertFormula(t3);
  Term t5 = solver.getInterpolant(t3);

  return 0;
}
