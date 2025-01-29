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
 * Test for project issue #567
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  solver.setOption("preregister-mode", "lazy");
  solver.setOption("produce-abducts", "true");
  solver.setOption("preprocess-only", "true");
  solver.setOption("fp-exp", "true");
  Sort s0 = tm.mkFloatingPointSort(5, 11);
  Term t1 = tm.mkFloatingPointPosZero(5, 11);
  Op o2 = tm.mkOp(Kind::FLOATINGPOINT_NEG);
  Term t3 = tm.mkTerm(o2, {t1});
  Term t4 = tm.mkTerm(Kind::FLOATINGPOINT_IS_POS, {t3});
  Sort s5 = t4.getSort();
  Term t6 = solver.getAbduct(t4);
  return 0;
}
