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
 * Testing stuff that is not exposed by the Java API to fix code coverage
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

  ASSERT_THROW(d_solver.getValue(x), CVC5ApiRecoverableException);
  
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

TEST_F(TestApiBlackUncovered, hash)
{
    std::hash<Op>()(Op());
    std::hash<Sort>()(Sort());
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
}

TEST_F(TestApiBlackUncovered, Statistics)
{
    Stat stat;
    stat = Stat();
    Statistics stats = d_solver.getStatistics();
    auto it = stats.begin();
    it++;
    it--;
    ++it;
    --it;
}

}  // namespace test
}  // namespace cvc5::internal
