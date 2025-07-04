/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #334
 *
 */

#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver slv(tm);
  slv.setOption("produce-unsat-cores", "true");
  slv.setOption("strings-exp", "true");
  Sort s1 = tm.mkBitVectorSort(1);
  Sort s2 = tm.mkFloatingPointSort(8, 24);
  Term val = tm.mkBitVector(32, "10000000110010111010111011000101", 2);
  Term t1 = tm.mkFloatingPoint(8, 24, val);
  Term t2 = tm.mkConst(s1);
  Term t4 = tm.mkTerm(Kind::BITVECTOR_UBV_TO_INT, {t2});
  Term t5 = tm.mkTerm(Kind::STRING_FROM_CODE, {t4});
  Term t6 = slv.simplify(t5);
  Term t7 = tm.mkTerm(Kind::STRING_LEQ, {t5, t6});
  slv.assertFormula(t7);
  slv.simplify(t1);
}
