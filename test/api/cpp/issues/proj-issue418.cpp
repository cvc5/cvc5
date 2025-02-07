/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #418. Based on murxla output
 *
 */

#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_FP");
  slv.setOption("bool-to-bv", "all");
  slv.setOption("dag-thresh", "0");
  slv.setOption("fp-exp", "true");
  Sort s1 = tm.getRoundingModeSort();
  Term t1 = tm.mkConst(s1, "_x0");
  Term t15 = tm.mkConst(s1, "_x12");
  Term t16 = tm.mkConst(s1, "_x13");
  Term t19 = tm.mkTerm(Kind::EQUAL, {t1, t15});
  Term t63 = tm.mkTerm(Kind::DISTINCT, {t1, t16});
  Term t76 = tm.mkTerm(Kind::EQUAL, {t1, t1});
  Term t101 = tm.mkTerm(Kind::DISTINCT, {t76, t19});
  Term t102 = tm.mkTerm(Kind::OR, {t101, t19});
  Term t104 = tm.mkTerm(Kind::ITE, {t102, t19, t63});
  Term t105 = tm.mkTerm(Kind::ITE, {t104, t1, t15});
  Term t196 = tm.mkTerm(Kind::EQUAL, {t105, t1});
  Term t201 = tm.mkTerm(Kind::ITE, {t196, t1, t15});
  Sort s13 = tm.mkFloatingPointSort(5, 11);
  Term t436 = tm.mkConst(s13, "_x23");
  Term t450 = tm.mkTerm(Kind::FLOATINGPOINT_SQRT, {t1, t436});
  Term t785 = tm.mkTerm(Kind::FLOATINGPOINT_DIV, {t201, t436, t436});
  Term t788 = tm.mkTerm(Kind::FLOATINGPOINT_IS_NAN, {t785});
  slv.assertFormula({t788});
  (void)slv.simplify(t450);
}
