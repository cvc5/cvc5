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
 * Test for project issue #580
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  Solver solver;
  solver.setOption("incremental", "false");
  solver.setOption("produce-abducts", "true");
  solver.setOption("sygus-grammar-cons", "any-term-concise");
  Sort s0 = solver.getRealSort();
  Sort s1 = solver.mkSequenceSort(s0);
  Term t2 = solver.mkConst(s1, "_x0");
  Term t3 = solver.mkTerm(SEQ_UNIT, {t2});
  Sort s4 = t3.getSort();
  Op o5 = solver.mkOp(SEQ_CONTAINS);
  Term t6 = solver.mkTerm(o5, {t3, t3});
  Sort s7 = t6.getSort();
  solver.assertFormula(t6);
  Term t8 = solver.getAbduct(t6);

  return 0;
}
