/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Solver slv;
  slv.setLogic("QF_FP");
  slv.setOption("bool-to-bv", "all");
  slv.setOption("dag-thresh", "0");
  slv.setOption("fp-exp", "true");
  Sort s1 = slv.getRoundingModeSort();
  Term t1 = slv.mkConst(s1, "_x0");
  Term t15 = slv.mkConst(s1, "_x12");
  Term t16 = slv.mkConst(s1, "_x13");
  Term t19 = slv.mkTerm(Kind::EQUAL, {t1, t15});
  Term t63 = slv.mkTerm(Kind::DISTINCT, {t1, t16});
  Term t76 = slv.mkTerm(Kind::EQUAL, {t1, t1});
  Term t101 = slv.mkTerm(Kind::DISTINCT, {t76, t19});
  Term t102 = slv.mkTerm(Kind::OR, {t101, t19});
  Term t104 = slv.mkTerm(Kind::ITE, {t102, t19, t63});
  Term t105 = slv.mkTerm(Kind::ITE, {t104, t1, t15});
  Term t196 = slv.mkTerm(Kind::EQUAL, {t105, t1});
  Term t201 = slv.mkTerm(Kind::ITE, {t196, t1, t15});
  Sort s13 = slv.mkFloatingPointSort(5, 11);
  Term t436 = slv.mkConst(s13, "_x23");
  Term t450 = slv.mkTerm(Kind::FLOATINGPOINT_SQRT, {t1, t436});
  Term t785 = slv.mkTerm(Kind::FLOATINGPOINT_DIV, {t201, t436, t436});
  Term t788 = slv.mkTerm(Kind::FLOATINGPOINT_IS_NAN, {t785});
  slv.assertFormula({t788});
  (void) slv.simplify(t450);
}

