/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Solver slv(tm);
  slv.setOption("incremental", "true");
  slv.setOption("check-proofs", "true");
  Sort s1 = tm.getBooleanSort();
  Sort s2 = tm.getIntegerSort();
  Sort s3 = tm.mkBitVectorSort(81);
  Term t5 = tm.mkConst(s2, "_x4");
  Term t27 = tm.mkBoolean(false);
  Term t35 = tm.mkBitVector(81,
                            "01111101110010010010110100110101000100101001101000"
                            "0111011010001110001111010101100",
                            2);
  Term t37 = tm.mkTerm(Kind::BITVECTOR_UBV_TO_INT, {t35});
  Term t40 = tm.mkTerm(Kind::PI);
  Term t43 = tm.mkTerm(Kind::ADD, {t40, t40});
  Term t45 = tm.mkTerm(tm.mkOp(Kind::IAND, {31}), {t37, t5});
  Term t66 = tm.mkTerm(Kind::EQUAL, {t43, t40});
  Term t101 = tm.mkTerm(Kind::LT, {t37, t45});
  slv.assertFormula({t66});
  Term t102 = tm.mkTerm(Kind::AND, {t101, t27, t101, t101});
  Term t103 = tm.mkTerm(Kind::NOT, {t102});
  slv.checkSatAssuming({t103});
  Term t104 = tm.mkTerm(Kind::NOT, {t101});
  slv.checkSatAssuming({t104});
}
