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
 * Test for project issue #567
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("preregister-mode", "lazy");
  solver.setOption("produce-abducts", "true");
  solver.setOption("preprocess-only", "true");
  Sort s0 = solver.mkFloatingPointSort(5, 11);
  Term t1 = solver.mkFloatingPointPosZero(5, 11);
  Op o2 = solver.mkOp(FLOATINGPOINT_NEG);
  Term t3 = solver.mkTerm(o2, {t1});
  Term t4 = solver.mkTerm(FLOATINGPOINT_IS_POS, {t3});
  Sort s5 = t4.getSort();
  Term t6 = solver.getAbduct(t4);

  return 0;
}
