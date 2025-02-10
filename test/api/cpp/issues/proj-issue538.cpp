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
 * Test for project issue #538
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  Sort s0 = tm.mkBitVectorSort(128);
  Term t1 = tm.mkConst(s0, "_x2");
  Op o2 = tm.mkOp(Kind::BITVECTOR_TO_NAT);
  Term t3 = tm.mkTerm(o2, {t1});
  Sort s4 = t3.getSort();
  Op o5 = tm.mkOp(Kind::INT_TO_BITVECTOR, {27});
  Term t6 = tm.mkTerm(o5, {t3});
  Sort s7 = t6.getSort();
  Op o8 = tm.mkOp(Kind::BITVECTOR_SGE);
  Term t9 = tm.mkTerm(o8, {t6, t6});
  Sort s10 = t9.getSort();
  solver.checkSatAssuming({t9, t9});
  return 0;
}
