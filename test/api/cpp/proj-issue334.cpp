/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Solver slv;
  slv.setOption("produce-unsat-cores", "true");
  slv.setOption("strings-exp", "true");
  Sort s1 = slv.mkBitVectorSort(1);
  Sort s2 = slv.mkFloatingPointSort(8, 24);
  Term val = slv.mkBitVector(32, "10000000110010111010111011000101", 2);
  Term t1 = slv.mkFloatingPoint(8, 24, val);
  Term t2 = slv.mkConst(s1);
  Term t4 = slv.mkTerm(Kind::BITVECTOR_TO_NAT, {t2});
  Term t5 = slv.mkTerm(Kind::STRING_FROM_CODE, {t4});
  Term t6 = slv.simplify(t5);
  Term t7 = slv.mkTerm(Kind::STRING_LEQ, {t5, t6});
  slv.assertFormula(t7);
  slv.simplify(t1);
}
