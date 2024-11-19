/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("produce-interpolants", "true");
  solver.setOption("preprocess-only", "true");
  solver.setOption("preregister-mode", "lazy");
  Sort s0 = tm.getIntegerSort();
  Term t1 = tm.mkInteger("842737");
  Term t2 = tm.mkInteger("4673842139166733208409");
  Term t3 = tm.mkInteger("651450683408549550470379592992505613867725244404");
  Op o4 = tm.mkOp(Kind::SUB);
  Term t5 = tm.mkTerm(o4, {t3, t1});
  Term t6 = tm.mkTerm(Kind::GEQ, {t2, t5});
  Sort s7 = t6.getSort();
  Term t8 = solver.getInterpolant(t6);

  return 0;
}
