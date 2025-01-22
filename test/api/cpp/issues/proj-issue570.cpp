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
 * Test for project issue #570
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
  Sort s0 = tm.getStringSort();
  Term t1 = tm.mkString("");
  Op o2 = tm.mkOp(Kind::SET_SINGLETON);
  Term t3 = tm.mkTerm(o2, {t1});
  Sort s4 = t3.getSort();
  Op o5 = tm.mkOp(Kind::SET_MINUS);
  Term t6 = tm.mkTerm(o5, {t3, t3});
  Op o7 = tm.mkOp(Kind::SET_IS_SINGLETON);
  Term t8 = tm.mkTerm(o7, {t6});
  Sort s9 = t8.getSort();
  Term t10 = solver.getInterpolant(t8);

  return 0;
}
