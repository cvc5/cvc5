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
  (void)d_solver->synthFun("f", {}, d_tm.getBooleanSort());
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
  cvc5::SynthResult res_null;
  ASSERT_FALSE(res_null.hasNoSolution());
}

TEST_F(TestApiBlackSynthResult, isUnknown)
{
  d_solver->setOption("sygus", "true");
  (void)d_solver->synthFun("f", {}, d_tm.getBooleanSort());
  Term boolTerm = d_tm.mkFalse();
  d_solver->addSygusConstraint(boolTerm);
  cvc5::SynthResult res = d_solver->checkSynth();
  ASSERT_FALSE(res.isNull());
  ASSERT_FALSE(res.hasSolution());
  ASSERT_TRUE(res.hasNoSolution());
  ASSERT_FALSE(res.isUnknown());
}

TEST_F(TestApiBlackSynthResult, equal)
{
  d_solver->setOption("sygus", "true");
  (void)d_solver->synthFun("f", {}, d_bool);
  Term tfalse = d_tm.mkFalse();
  Term ttrue = d_tm.mkTrue();
  d_solver->addSygusConstraint(ttrue);
  cvc5::SynthResult res1 = d_solver->checkSynth();
  d_solver->addSygusConstraint(tfalse);
  cvc5::SynthResult res2 = d_solver->checkSynth();
  ASSERT_EQ(res1, res1);
  ASSERT_NE(res1, res2);
  ASSERT_NE(res1, cvc5::SynthResult());
  ASSERT_NE(cvc5::SynthResult(), res1);
}

TEST_F(TestApiBlackSynthResult, hash)
{
  d_solver->setOption("sygus", "true");
  (void)d_solver->synthFun("f", {}, d_bool);
  Term tfalse = d_tm.mkFalse();
  Term ttrue = d_tm.mkTrue();
  d_solver->addSygusConstraint(ttrue);
  d_solver->addSygusConstraint(ttrue);
  cvc5::SynthResult res1 = d_solver->checkSynth();
  d_solver->addSygusConstraint(tfalse);
  cvc5::SynthResult res2 = d_solver->checkSynth();
  ASSERT_EQ(std::hash<cvc5::SynthResult>{}(res1),
            std::hash<cvc5::SynthResult>{}(res1));
  ASSERT_NE(std::hash<cvc5::SynthResult>{}(res1),
            std::hash<cvc5::SynthResult>{}(res2));
  ASSERT_NE(std::hash<cvc5::SynthResult>{}(cvc5::SynthResult()),
            std::hash<cvc5::SynthResult>{}(res2));
}

}  // namespace test
}  // namespace cvc5::internal
