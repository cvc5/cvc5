/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #423.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("produce-models", "true");
  solver.setOption("produce-difficulty", "true");
  Sort s2 = tm.getRealSort();
  Sort s3 = tm.mkSequenceSort(s2);
  Term t2;
  {
    t2 = tm.mkEmptySequence(s3.getSequenceElementSort());
  }
  Term t22 = tm.mkReal("119605652059157009");
  Term t32 = tm.mkTerm(Kind::SEQ_UNIT, {t22});
  Term t43 = tm.mkTerm(Kind::SEQ_CONCAT, {t2, t32});
  Term t51 = tm.mkTerm(Kind::DISTINCT, {t32, t32});
  solver.checkSat();
  solver.blockModelValues({t51, t43});
}
