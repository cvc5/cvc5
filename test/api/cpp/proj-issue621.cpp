/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #621
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-interpolants", "true");
  solver.setOption("preprocess-only", "true");
  solver.setOption("preregister-mode", "lazy");
  Sort s0 = solver.getIntegerSort();
  Term t1 = solver.mkInteger("842737");
  Term t2 = solver.mkInteger("4673842139166733208409");
  Term t3 =
      solver.mkInteger("651450683408549550470379592992505613867725244404");
  Op o4 = solver.mkOp(SUB);
  Term t5 = solver.mkTerm(o4, {t3, t1});
  Term t6 = solver.mkTerm(GEQ, {t2, t5});
  Sort s7 = t6.getSort();
  Term t8 = solver.getInterpolant(t6);

  return 0;
}
