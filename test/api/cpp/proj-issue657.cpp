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
 * Test for project issue #657
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-interpolants", "true");
  solver.setOption("prenex-quant", "norm");
  Sort s0 = solver.getStringSort();
  Term t1 = solver.mkVar(s0, "_x3");
  Op o2 = solver.mkOp(Kind::STRING_CONCAT);
  Term t3 = solver.mkTerm(o2, {t1, t1});
  Term t4 = t1.eqTerm(t3);
  Sort s5 = t4.getSort();
  Term t6 = solver.mkTerm(Kind::VARIABLE_LIST, {t1});
  Sort s7 = t6.getSort();
  Op o8 = solver.mkOp(Kind::EXISTS);
  Term t9 = solver.mkTerm(o8, {t6, t4});
  Term t10 = solver.getInterpolant(t9);

  return 0;
}
