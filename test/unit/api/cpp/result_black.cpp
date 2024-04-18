/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Result class
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackResult : public TestApi
{
};

TEST_F(TestApiBlackResult, isNull)
{
  cvc5::Result res_null;
  ASSERT_TRUE(res_null.isNull());
  ASSERT_FALSE(res_null.isSat());
  ASSERT_FALSE(res_null.isUnsat());
  ASSERT_FALSE(res_null.isUnknown());
  Sort u_sort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkConst(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  cvc5::Result res = d_solver->checkSat();
  ASSERT_FALSE(res.isNull());
}

TEST_F(TestApiBlackResult, eq)
{
  Sort u_sort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkConst(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  cvc5::Result res;
  cvc5::Result res2 = d_solver->checkSat();
  cvc5::Result res3 = d_solver->checkSat();
  ASSERT_NE(res, res2);
  res = res2;
  ASSERT_EQ(res, res2);
  ASSERT_EQ(res3, res2);
  {
    std::stringstream ss;
    ss << res;
    ASSERT_EQ(res.toString(), "sat");
    ASSERT_EQ(res.toString(), ss.str());
  }
}

TEST_F(TestApiBlackResult, isSat)
{
  Sort u_sort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkConst(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x));
  cvc5::Result res = d_solver->checkSat();
  ASSERT_TRUE(res.isSat());
  ASSERT_FALSE(res.isUnknown());
}

TEST_F(TestApiBlackResult, isUnsat)
{
  Sort u_sort = d_tm.mkUninterpretedSort("u");
  Term x = d_tm.mkConst(u_sort, "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());
  cvc5::Result res = d_solver->checkSat();
  ASSERT_TRUE(res.isUnsat());
  ASSERT_FALSE(res.isUnknown());
}

TEST_F(TestApiBlackResult, isUnknown)
{
  d_solver->setLogic("QF_NIA");
  d_solver->setOption("incremental", "false");
  d_solver->setOption("solve-real-as-int", "true");
  Sort real_sort = d_tm.getRealSort();
  Term x = d_tm.mkConst(real_sort, "x");
  d_solver->assertFormula(d_tm.mkTerm(Kind::LT, {d_tm.mkReal("0.0"), x}));
  d_solver->assertFormula(d_tm.mkTerm(Kind::LT, {x, d_tm.mkReal("1.0")}));
  cvc5::Result res = d_solver->checkSat();
  ASSERT_FALSE(res.isSat());
  ASSERT_TRUE(res.isUnknown());
  cvc5::UnknownExplanation ue = res.getUnknownExplanation();
  ASSERT_EQ(ue, cvc5::UnknownExplanation::UNKNOWN_REASON);
  {
    std::stringstream ss;
    ss << ue;
    ASSERT_EQ(ss.str(), "UNKNOWN_REASON");
  }
}

}  // namespace test
}  // namespace cvc5::internal
