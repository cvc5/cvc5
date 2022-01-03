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
  slv.setOption("nl-cad", "true");
  slv.setOption("nl-cad-var-elim", "true");
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

}  // namespace test
}  // namespace cvc5
