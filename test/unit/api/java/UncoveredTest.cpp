/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

TEST_F(TestApiBlackUncovered, comparison_operators)
{
  cvc5::Result res;
  res != res;
  cvc5::Sort sort;
  sort != sort;
  sort <= sort;
  sort >= sort;
  sort > sort;
  cvc5::Op op;
  op != op;
  cvc5::Term term;
  term != term;
  term <= term;
  term >= term;
  term > term;
}

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

TEST_F(TestApiBlackUncovered, term_native_types)
{
  Term t = d_solver.mkInteger(0);
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

TEST_F(TestApiBlackUncovered, term_iterators)
{
  Term t = d_solver.mkInteger(0);
  t = d_solver.mkTerm(Kind::GT, {t, t});
  Term::const_iterator it;
  it = t.begin();
  auto it2(it);
  it == t.end();
  it != it2;
  *it2;
  ++it;
  it++;
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

TEST_F(TestApiBlackUncovered, mkString)
{
  std::wstring s;
  ASSERT_EQ(d_solver.mkString(s).getStringValue(), s);
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
    testing::internal::CaptureStdout();
    d_solver.printStatisticsSafe(STDOUT_FILENO);
    testing::internal::GetCapturedStdout();
}

TEST_F(TestApiBlackUncovered, Datatypes)
{
  // default constructors
  DatatypeConstructorDecl dtcd;
  DatatypeSelector dts;
  DatatypeConstructor dc;
  DatatypeDecl dtd;
  Datatype d;

  dtd = d_solver.mkDatatypeDecl("list");
  dtcd = d_solver.mkDatatypeConstructorDecl("cons");
  dtcd.addSelector("head", d_solver.getIntegerSort());
  dtd.addConstructor(dtcd);
  Sort s = d_solver.mkDatatypeSort(dtd);
  d = s.getDatatype();
  dc = d.getConstructor("cons");
  dc.getSelector("head");

  {
    Datatype::const_iterator it;
    it = d.begin();
    it != d.end();
    *it;
    it->getName();
    ++it;
    it == d.end();
    it++;
  }
  {
    DatatypeConstructor::const_iterator it;
    it = dc.begin();
    it != dc.end();
    *it;
    it->getName();
    ++it;
    it = dc.begin();
    it++;
    it == dc.end();
  }

  {
    std::stringstream ss;
    ss << d;
    ss << dtcd;
    ss << dc;
    ss << d.getSelector("head");
  }
}

}  // namespace test
}  // namespace cvc5::internal
