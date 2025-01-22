/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #455
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

#include "base/configuration.h"

using namespace cvc5;

int main(void)
{
  if (!internal::Configuration::isBuiltWithPoly())
  {
    return 0;
  }
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_UFNRA");
  slv.setOption("produce-unsat-assumptions", "true");
  slv.setOption("incremental", "false");
  slv.setOption("produce-models", "true");
  Sort s1 = tm.mkUninterpretedSort("_u0");
  Sort s2 = tm.getRealSort();
  Term t1 = tm.mkConst(s2, "_x4");
  Term t2 = tm.mkConst(s1, "_x5");
  Term t3 = tm.mkConst(s2, "_x7");
  Term t4 = tm.mkReal("2");
  Term t5 = tm.mkConst(s2, "_x10");
  Term t6 = tm.mkConst(s2, "_x11");
  Term t7 = tm.mkReal("3615783917");
  Term t8 = tm.mkConst(s2, "_x14");
  Term t9 = tm.mkConst(s2, "_x15");
  Term t10 = tm.mkTerm(Kind::ADD, {t5, t9});
  Term t11 = tm.mkTerm(Kind::ADD, {t10, t7, t8, t6});
  Term t12 = tm.mkTerm(Kind::LEQ, {t4, t11});
  Term t13 = tm.mkTerm(Kind::SUB, {t11, t6});
  Term t14 = tm.mkTerm(Kind::SUB, {t6, t13});
  Term t15 = tm.mkTerm(Kind::MULT, {t4, t4});
  Term t16 = tm.mkTerm(Kind::GT, {t15, t11});
  Term t17 = tm.mkTerm(Kind::SUB, {t11, t3});
  Term t18 = tm.mkTerm(Kind::LEQ, {t17, t7});
  Term t19 = tm.mkTerm(Kind::IMPLIES, {t18, t12});
  Term t20 = tm.mkTerm(Kind::GEQ, {t1, t3});
  Term t21 = tm.mkTerm(Kind::MULT, {t7, t13});
  Term t22 = tm.mkTerm(Kind::MULT, {t21, t14});
  Term t23 = tm.mkTerm(Kind::SUB, {t14, t3});
  Term t24 = tm.mkVar(s2, "_f19_0");
  Term t25 = tm.mkVar(s2, "_f19_1");
  Term t26 = tm.mkVar(s1, "_f19_2");
  Term t27 = tm.mkVar(s2, "_f19_3");
  Term t28 = tm.mkVar(s1, "_f19_4");
  Term t29 =
      slv.defineFun("_f19", {t24, t25, t26, t27, t28}, t24.getSort(), t24);
  Term t30 = tm.mkTerm(Kind::DISTINCT, {t19, t20, t16});
  Term t31 = tm.mkTerm(Kind::ITE, {t30, t9, t22});
  Term t32 = tm.mkTerm(Kind::DIVISION, {t11, t6, t10});
  Term t33 = tm.mkTerm(Kind::GEQ, {t32, t3});
  Term t34 = tm.mkTerm(Kind::APPLY_UF, {t29, t31, t3, t2, t3, t2});
  Term t35 = tm.mkTerm(Kind::GEQ, {t34, t23});
  Term t36 = tm.mkTerm(Kind::NOT, {t35});
  slv.assertFormula({t36});
  slv.assertFormula({t33});
  slv.checkSatAssuming({t18.notTerm()});
}
