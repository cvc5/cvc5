/*********************                                                        */
/*! \file result_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Result class
 **/

#include "test_api.h"

namespace CVC4 {

using namespace api;

namespace test {

class TestApiResultBlack : public TestApi
{
};

TEST_F(TestApiResultBlack, isNull)
{
  CVC4::api::Result res_null;
  ASSERT_TRUE(res_null.isNull());
  ASSERT_FALSE(res_null.isSat());
  ASSERT_FALSE(res_null.isUnsat());
  ASSERT_FALSE(res_null.isSatUnknown());
  ASSERT_FALSE(res_null.isEntailed());
  ASSERT_FALSE(res_null.isNotEntailed());
  ASSERT_FALSE(res_null.isEntailmentUnknown());
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  CVC4::api::Result res = d_solver.checkSat();
  ASSERT_FALSE(res.isNull());
}

TEST_F(TestApiResultBlack, eq)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  CVC4::api::Result res;
  CVC4::api::Result res2 = d_solver.checkSat();
  CVC4::api::Result res3 = d_solver.checkSat();
  res = res2;
  ASSERT_EQ(res, res2);
  ASSERT_EQ(res3, res2);
}

TEST_F(TestApiResultBlack, isSat)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  CVC4::api::Result res = d_solver.checkSat();
  ASSERT_TRUE(res.isSat());
  ASSERT_FALSE(res.isSatUnknown());
}

TEST_F(TestApiResultBlack, isUnsat)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkVar(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  CVC4::api::Result res = d_solver.checkSat();
  ASSERT_TRUE(res.isUnsat());
  ASSERT_FALSE(res.isSatUnknown());
}

TEST_F(TestApiResultBlack, isSatUnknown)
{
  d_solver.setLogic("QF_NIA");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver.getIntegerSort();
  Term x = d_solver.mkVar(int_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  CVC4::api::Result res = d_solver.checkSat();
  ASSERT_FALSE(res.isSat());
  ASSERT_TRUE(res.isSatUnknown());
}

TEST_F(TestApiResultBlack, isEntailed)
{
  d_solver.setOption("incremental", "true");
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(u_sort, "x");
  Term y = d_solver.mkConst(u_sort, "y");
  Term a = x.eqTerm(y).notTerm();
  Term b = x.eqTerm(y);
  d_solver.assertFormula(a);
  CVC4::api::Result entailed = d_solver.checkEntailed(a);
  ASSERT_TRUE(entailed.isEntailed());
  ASSERT_FALSE(entailed.isEntailmentUnknown());
  CVC4::api::Result not_entailed = d_solver.checkEntailed(b);
  ASSERT_TRUE(not_entailed.isNotEntailed());
  ASSERT_FALSE(not_entailed.isEntailmentUnknown());
}

TEST_F(TestApiResultBlack, isEntailmentUnknown)
{
  d_solver.setLogic("QF_NIA");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver.getIntegerSort();
  Term x = d_solver.mkVar(int_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  CVC4::api::Result res = d_solver.checkEntailed(x.eqTerm(x));
  ASSERT_FALSE(res.isEntailed());
  ASSERT_TRUE(res.isEntailmentUnknown());
  ASSERT_EQ(res.getUnknownExplanation(), "UNKNOWN_REASON");
}
}  // namespace test
}  // namespace CVC4
