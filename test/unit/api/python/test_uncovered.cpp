/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Testing stuff that is not exposed by the python API to fix code coverage
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackUncovered : public TestApi
{
};

TEST_F(TestApiBlackUncovered, exception_getmessage)
{
  d_solver.setOption("produce-models", "true");
  Term x = d_solver.mkConst(d_solver.getBooleanSort(), "x");
  d_solver.assertFormula(x.eqTerm(x).notTerm());
  
  try {
    d_solver.getValue(x);
  }
  catch (const CVC5ApiRecoverableException& e)
  {
    ASSERT_NO_THROW(e.getMessage());
  }
}

TEST_F(TestApiBlackUncovered, streaming_operators)
{
  std::stringstream ss;
  ss << cvc5::modes::LearnedLitType::PREPROCESS;
  ss << cvc5::Result();
  ss << cvc5::Op();
  ss << cvc5::SynthResult();

  Sort intsort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intsort, "x");

  ss << std::vector<Term>{x, x};
  ss << std::set<Term>{x, x};
  ss << std::unordered_set<Term>{x, x};
}

TEST_F(TestApiBlackUncovered, getValue)
{
  d_solver.setOption("produce-models", "true");
  Sort boolsort = d_solver.getBooleanSort();
  Term b = d_solver.mkConst(boolsort, "b");
  d_solver.assertFormula(b);
  d_solver.checkSat();
  d_solver.getValue({b, b, b});
}

TEST_F(TestApiBlackUncovered, isOutputOn)
{
  d_solver.isOutputOn("inst");
  d_solver.getOutput("inst");
}

TEST_F(TestApiBlackUncovered, Options)
{
    auto dopts = d_solver.getDriverOptions();
    dopts.err();
    dopts.in();
    dopts.out();

    std::stringstream ss;
    {
        auto info = d_solver.getOptionInfo("verbose");
        ss << info;
    }
    {
        auto info = d_solver.getOptionInfo("print-success");
        ss << info;
        info.boolValue();
    }
    {
        auto info = d_solver.getOptionInfo("verbosity");
        ss << info;
        info.intValue();
    }
    {
        auto info = d_solver.getOptionInfo("rlimit");
        ss << info;
        info.uintValue();
    }
    {
        auto info = d_solver.getOptionInfo("random-freq");
        ss << info;
        info.doubleValue();
    }
    {
        auto info = d_solver.getOptionInfo("force-logic");
        ss << info;
        info.stringValue();
    }
    {
        auto info = d_solver.getOptionInfo("simplification");
        ss << info;
    }
}

TEST_F(TestApiBlackUncovered, Statistics)
{
    d_solver.assertFormula(d_solver.mkConst(d_solver.getBooleanSort(), "x"));
    d_solver.checkSat();
    Statistics stats = d_solver.getStatistics();
    std::stringstream ss;
    ss << stats;
    auto it = stats.begin();
    ASSERT_NE(it, stats.end());
    it++;
    it--;
    ++it;
    --it;
    ASSERT_EQ(it, stats.begin());
    ss << it->first;

}

}  // namespace test
}  // namespace cvc5::internal
