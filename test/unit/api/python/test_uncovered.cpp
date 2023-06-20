/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  ss << cvc5::SortKind::ARRAY_SORT;
  ss << cvc5::UnknownExplanation::UNKNOWN_REASON;
  ss << cvc5::modes::BlockModelsMode::LITERALS;
  ss << cvc5::modes::LearnedLitType::LEARNED_LIT_PREPROCESS;
  ss << cvc5::modes::ProofComponent::PROOF_COMPONENT_FULL;
  ss << cvc5::modes::FindSynthTarget::FIND_SYNTH_TARGET_ENUM;
  ss << cvc5::Result();
  ss << cvc5::Op();
  ss << cvc5::SynthResult();
  ss << cvc5::Grammar();

  Sort intsort = d_solver.getIntegerSort();
  Term x = d_solver.mkConst(intsort, "x");

  ss << std::vector<Term>{x, x};
  ss << std::set<Term>{x, x};
  ss << std::unordered_set<Term>{x, x};
}

TEST_F(TestApiBlackUncovered, datatypeApi)
{
  DatatypeDecl dtypeSpec = d_solver.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_solver.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_solver.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_solver.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort listSort = d_solver.mkDatatypeSort(dtypeSpec);
  Datatype d = listSort.getDatatype();

  std::stringstream ss;
  ss << cons;
  ss << d.getConstructor("cons");
  ss << d.getSelector("head");
  ss << std::vector<DatatypeConstructorDecl>{cons, nil};
  ss << d;

  {
    DatatypeConstructor c = d.getConstructor("cons");
    DatatypeConstructor::const_iterator it;
    it = c.begin();
    ASSERT_NE(it, c.end());
    ASSERT_EQ(it, c.begin());
    *it;
    ASSERT_NO_THROW(it->getName());
    ++it;
    it++;
  }
  {
    Datatype::const_iterator it;
    it = d.begin();
    ASSERT_NE(it, d.end());
    ASSERT_EQ(it, d.begin());
    it->getName();
    *it;
    ++it;
    it++;
  }
}

TEST_F(TestApiBlackUncovered, termNativeTypes)
{
  Term t = d_solver.mkInteger(0);
  d_solver.mkReal(0);
  d_solver.mkReal(0, 1);
  t.isInt32Value();
  t.getInt32Value();
  t.isInt64Value();
  t.getInt64Value();
  t.isUInt32Value();
  t.getUInt32Value();
  t.isUInt64Value();
  t.getUInt64Value();
  t.isReal32Value();
  t.getReal32Value();
  t.isReal64Value();
  t.getReal64Value();
}

TEST_F(TestApiBlackUncovered, termIterators)
{
  Term t = d_solver.mkInteger(0);
  auto it = t.begin();
  auto it2(it);
  it++;
}

TEST_F(TestApiBlackUncovered, checkSatAssumingSingle)
{
  Sort boolsort = d_solver.getBooleanSort();
  Term b = d_solver.mkConst(boolsort, "b");
  d_solver.checkSatAssuming(b);
}

TEST_F(TestApiBlackUncovered, mkOpInitializerList)
{
  d_solver.mkOp(Kind::BITVECTOR_EXTRACT, {1, 1});
}

TEST_F(TestApiBlackUncovered, mkTermKind)
{
  Term b = d_solver.mkConst(d_solver.getRealSort(), "b");
  d_solver.mkTerm(Kind::GT, {b, b});
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

    testing::internal::CaptureStdout();
    d_solver.printStatisticsSafe(STDOUT_FILENO);
    testing::internal::GetCapturedStdout();
}

// Copied from api/cpp/solver_black.cpp
TEST_F(TestApiBlackUncovered, declareOracleFunUnsat)
{
  d_solver.setOption("oracles", "true");
  Sort iSort = d_solver.getIntegerSort();
  // f is the function implementing (lambda ((x Int)) (+ x 1))
  Term f = d_solver.declareOracleFun(
      "f", {iSort}, iSort, [&](const std::vector<Term>& input) {
        if (input[0].isUInt32Value())
        {
          return d_solver.mkInteger(input[0].getUInt32Value() + 1);
        }
        return d_solver.mkInteger(0);
      });
  Term three = d_solver.mkInteger(3);
  Term five = d_solver.mkInteger(5);
  Term eq =
      d_solver.mkTerm(EQUAL, {d_solver.mkTerm(APPLY_UF, {f, three}), five});
  d_solver.assertFormula(eq);
  d_solver.checkSat();
}

}  // namespace test
}  // namespace cvc5::internal
