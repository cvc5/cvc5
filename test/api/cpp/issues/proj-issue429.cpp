/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #429.
 */

#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);
  Sort s1 = tm.getRealSort();
  Term t6 = tm.mkConst(s1, "_x5");
  Term t16 =
      tm.mkReal(std::stoll("1696223.9473797265702297792792306581323741"));
  Term t111 = tm.mkTerm(Kind::SEQ_UNIT, {t16});
  Term t119 = tm.mkTerm(tm.mkOp(Kind::SEQ_UNIT), {t6});
  Term t126 = tm.mkTerm(Kind::SEQ_PREFIX, {t111, t119});
  solver.checkSatAssuming({t126.notTerm()});
}
