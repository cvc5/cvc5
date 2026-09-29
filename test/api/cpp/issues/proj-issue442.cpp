/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #442
 *
 */
#include <cvc5/cvc5.h>

using namespace cvc5;
int main(void)
{
  TermManager tm;
  Solver solver(tm);
  solver.setOption("incremental", "false");
  // the original value 10516708485319108261 is now out of range
  solver.setOption("solve-int-as-bv", "4294967295");
  Sort s1 = tm.getStringSort();
  Term t1 = tm.mkConst(s1, "_x0");
  Term t12 = tm.mkTerm(Kind::EQUAL, {t1, t1});
  Term t13 = tm.mkTerm(Kind::SET_SINGLETON, {t12});
  Term t28 = tm.mkTerm(Kind::SET_CARD, {t13});
  Term t122 = tm.mkTerm(Kind::SUB, {t28, t28});
  Term t135 = tm.mkVar(t28.getSort(), "_f12_0");
  Term t136 = tm.mkVar(s1, "_f12_1");
  Term t137 = tm.mkVar(t28.getSort(), "_f12_2");
  Term t138 = tm.mkVar(s1, "_f12_3");
  Term t141 = tm.mkTerm(Kind::INTS_MODULUS, {t122, t122});
  Term t142 = tm.mkTerm(Kind::NEG, {t141});
  Term t143 =
      solver.defineFun("_f12", {t135, t136, t137, t138}, t142.getSort(), t142);
  (void)solver.simplify(t143);
  (void)solver.simplify(t142);

  return 0;
}
