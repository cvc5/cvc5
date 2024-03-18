/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SynthResult class
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackSynthResult : public TestApi
{
};

TEST_F(TestApiBlackSynthResult, isNull)
{
  cvc5::SynthResult res_null;
  ASSERT_TRUE(res_null.isNull());
  ASSERT_FALSE(res_null.hasSolution());
  ASSERT_FALSE(res_null.hasNoSolution());
  ASSERT_FALSE(res_null.isUnknown());
}

TEST_F(TestApiBlackSynthResult, hasSolution)
{
  d_solver->setOption("sygus", "true");
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());
  Term boolTerm = d_tm.mkTrue();
  d_solver->addSygusConstraint(boolTerm);
  cvc5::SynthResult res = d_solver->checkSynth();
  ASSERT_FALSE(res.isNull());
  ASSERT_TRUE(res.hasSolution());
  ASSERT_FALSE(res.hasNoSolution());
  ASSERT_FALSE(res.isUnknown());
  ASSERT_EQ(res.toString(), "(SOLUTION)");
  {
    std::stringstream ss;
    ss << res;
    ASSERT_EQ(res.toString(), ss.str());
  }
}

TEST_F(TestApiBlackSynthResult, hasNoSolution)
{
  // note that we never return synth result for which hasNoSolution is true
  // currently
  cvc5::SynthResult res_null;
  ASSERT_FALSE(res_null.hasNoSolution());
}

TEST_F(TestApiBlackSynthResult, isUnknown)
{
  d_solver->setOption("sygus", "true");
  Term f = d_solver->synthFun("f", {}, d_tm.getBooleanSort());
  Term boolTerm = d_tm.mkFalse();
  d_solver->addSygusConstraint(boolTerm);
  cvc5::SynthResult res = d_solver->checkSynth();
  ASSERT_FALSE(res.isNull());
  ASSERT_FALSE(res.hasSolution());
  ASSERT_TRUE(res.hasNoSolution());
  ASSERT_FALSE(res.isUnknown());
}

}  // namespace test
}  // namespace cvc5::internal
