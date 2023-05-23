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
 * Test for project issue #377
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  Solver slv;
  slv.setOption("incremental", "true");
  slv.setOption("check-proofs", "true");
  Sort s1 = slv.getBooleanSort();
  Sort s2 = slv.getIntegerSort();
  Sort s3 = slv.mkBitVectorSort(81);
  Term t5 = slv.mkConst(s2, "_x4");
  Term t27 = slv.mkBoolean(false);
  Term t35 = slv.mkBitVector(81, "011111011100100100101101001101010001001010011010000111011010001110001111010101100", 2);
  Term t37 = slv.mkTerm(Kind::BITVECTOR_TO_NAT, {t35});
  Term t40 = slv.mkTerm(Kind::PI);
  Term t43 = slv.mkTerm(Kind::ADD, {t40, t40});
  Term t45 = slv.mkTerm(slv.mkOp(Kind::IAND, {31}), {t37, t5});
  Term t66 = slv.mkTerm(Kind::EQUAL, {t43, t40});
  Term t101 = slv.mkTerm(Kind::LT, {t37, t45});
  slv.assertFormula({t66});
  Term t102 = slv.mkTerm(Kind::AND, {t101, t27, t101, t101});
  Term t103 = slv.mkTerm(Kind::NOT, {t102});
  slv.checkSatAssuming({t103});
  Term t104 = slv.mkTerm(Kind::NOT, {t101});
  slv.checkSatAssuming({t104});
}
