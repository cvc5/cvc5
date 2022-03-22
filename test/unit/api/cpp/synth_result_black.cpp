/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SynthResult class
 */

#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiBlackSynthResult : public TestApi
{
};

TEST_F(TestApiBlackSynthResult, isNull)
{
  cvc5::api::SynthResult res_null;
  ASSERT_TRUE(res_null.isNull());
  ASSERT_FALSE(res_null.hasSolution());
  ASSERT_FALSE(res_null.hasNoSolution());
  ASSERT_FALSE(res_null.isUnknown());
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  cvc5::api::SynthResult res = d_solver.checkSynth();
  ASSERT_FALSE(res.isNull());
}

TEST_F(TestApiBlackSynthResult, hasSolution)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x));
  cvc5::api::SynthResult res = d_solver.checkSynth();
  ASSERT_TRUE(res.hasSolution());
  ASSERT_FALSE(res.isUnknown());
}

TEST_F(TestApiBlackSynthResult, hasNoSolution)
{
  Sort u_sort = d_solver.mkUninterpretedSort("u");
  Term x = d_solver.mkConst(u_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  cvc5::api::SynthResult res = d_solver.checkSynth();
  ASSERT_TRUE(res.hasNoSolution());
  ASSERT_FALSE(res.isUnknown());
}

TEST_F(TestApiBlackSynthResult, isUnknown)
{
  d_solver.setLogic("QF_NIA");
  d_solver.setOption("incremental", "false");
  d_solver.setOption("solve-int-as-bv", "32");
  Sort int_sort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(int_sort, "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  cvc5::api::SynthResult res = d_solver.checkSynth();
  ASSERT_FALSE(res.hasSolution());
  ASSERT_TRUE(res.isUnknown());
}

}  // namespace test
}  // namespace cvc5
