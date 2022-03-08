/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Blackbox tests using the API targeting nonlinear arithmetic.
 */

#include "test_api.h"
#include "base/configuration.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestTheoryBlackArithNl : public TestApi
{
};

TEST_F(TestTheoryBlackArithNl, cvc5Projects388)
{
  if (!Configuration::isBuiltWithPoly())
  {
    return;
  }
  Solver slv;
  slv.setLogic("QF_NRA");
  Sort s = slv.getRealSort();
  Term t1 = slv.mkConst(s, "a");
  Term t2 = slv.mkConst(s, "b");
  Term t3 = slv.mkConst(s, "c");
  Term t4 = slv.mkTerm(Kind::DIVISION, {t1, t2});
  Term t5 = slv.mkTerm(Kind::GT, {t4, t3});
  Term t6 = slv.mkTerm(Kind::DIVISION, {t1, t3});
  Term t7 = slv.mkTerm(Kind::IS_INTEGER, {t6});
  Term t8 = slv.mkTerm(Kind::AND, {t5, t7, t5});
  Term t9 = slv.mkTerm(Kind::NOT, {t8});
  slv.assertFormula(t9);
  slv.checkSat();
}

TEST_F(TestTheoryBlackArithNl, cvc5Projects388Min)
{
  if (!Configuration::isBuiltWithPoly())
  {
    return;
  }
  Solver slv;
  slv.setOption("nl-cov", "true");
  slv.setOption("nl-cov-var-elim", "true");
  slv.setOption("nl-ext", "none");
  slv.setLogic("QF_NIRA");
  Sort s = slv.getRealSort();
  Term t1 = slv.mkConst(s, "a");
  Term t2 = slv.mkConst(s, "b");
  Term t3 = slv.mkReal(0);
  Term t7 = slv.mkTerm(Kind::IS_INTEGER, {t1});
  Term t4 = slv.mkTerm(Kind::DIVISION, {t2, t1});
  Term t5 = slv.mkTerm(Kind::DISTINCT, {t3, t4});
  Term t8 = slv.mkTerm(Kind::OR, {t7, t5});
  slv.assertFormula(t8);
  slv.checkSat();
}

TEST_F(TestTheoryBlackArithNl, proj_issue421)
{
  Solver slv;
  slv.setLogic("QF_ALL");
  Sort s1 = slv.mkBitVectorSort(4);
  Sort s4 = slv.getRealSort();
  Sort s5 = slv.mkSequenceSort(s1);
  Term t8 = slv.mkConst(s5, "_x49");
  Term t10 = slv.mkConst(s4, "_x51");
  Term t65 = slv.mkTerm(Kind::SEQ_REV, {t8});
  Term t69 = slv.mkTerm(Kind::TANGENT, {t10});
  Term t77 = slv.mkTerm(Kind::LEQ, {t69, t10});
  Term t128 = slv.mkTerm(Kind::SEQ_PREFIX, {t65, t8});
  slv.assertFormula({t77});
  slv.checkEntailed({1, t128});
}

TEST_F(TestTheoryBlackArithNl, cvc5Projects455)
{
  Solver slv;
  slv.setLogic("QF_UFNRA");
  slv.setOption("produce-unsat-assumptions", "true");
  slv.setOption("incremental", "false");
  slv.setOption("produce-models", "true");
  Sort s1 = slv.mkUninterpretedSort("_u0");
  Sort s2 = slv.getRealSort();
  Term t1 = slv.mkConst(s2, "_x4");
  Term t2 = slv.mkConst(s1, "_x5");
  Term t3 = slv.mkConst(s2, "_x7");
  Term t4 = slv.mkReal("2");
  Term t5 = slv.mkConst(s2, "_x10");
  Term t6 = slv.mkConst(s2, "_x11");
  Term t7 = slv.mkReal("3615783917");
  Term t8 = slv.mkConst(s2, "_x14");
  Term t9 = slv.mkConst(s2, "_x15");
  Term t10 = slv.mkTerm(Kind::ADD, {t5, t9});
  Term t11 = slv.mkTerm(Kind::ADD, {t10, t7, t8, t6});
  Term t12 = slv.mkTerm(Kind::LEQ, {t4, t11});
  Term t13 = slv.mkTerm(Kind::SUB, {t11, t6});
  Term t14 = slv.mkTerm(Kind::SUB, {t6, t13});
  Term t15 = slv.mkTerm(Kind::MULT, {t4, t4});
  Term t16 = slv.mkTerm(Kind::GT, {t15, t11});
  Term t17 = slv.mkTerm(Kind::SUB, {t11, t3});
  Term t18 = slv.mkTerm(Kind::LEQ, {t17, t7});
  Term t19 = slv.mkTerm(Kind::IMPLIES, {t18, t12});
  Term t20 = slv.mkTerm(Kind::GEQ, {t1, t3});
  Term t21 = slv.mkTerm(Kind::MULT, {t7, t13});
  Term t22 = slv.mkTerm(Kind::MULT, {t21, t14});
  Term t23 = slv.mkTerm(Kind::SUB, {t14, t3});
  Term t24 = slv.mkVar(s2, "_f19_0");
  Term t25 = slv.mkVar(s2, "_f19_1");
  Term t26 = slv.mkVar(s1, "_f19_2");
  Term t27 = slv.mkVar(s2, "_f19_3");
  Term t28 = slv.mkVar(s1, "_f19_4");
  Term t29 = slv.defineFun("_f19", {t24, t25, t26, t27, t28}, t24.getSort(), t24);
  Term t30 = slv.mkTerm(Kind::DISTINCT, {t19, t20, t16});
  Term t31 = slv.mkTerm(Kind::ITE, {t30, t9, t22});
  Term t32 = slv.mkTerm(Kind::DIVISION, {t11, t6, t10});
  Term t33 = slv.mkTerm(Kind::GEQ, {t32, t3});
  Term t34 = slv.mkTerm(Kind::APPLY_UF, {t29, t31, t3, t2, t3, t2});
  Term t35 = slv.mkTerm(Kind::GEQ, {t34, t23});
  Term t36 = slv.mkTerm(Kind::NOT, {t35});
  slv.assertFormula({t36});
  slv.assertFormula({t33});
  slv.checkEntailed({t18});
}

}  // namespace test
}  // namespace cvc5
