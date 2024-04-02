/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Testing stuff that is not exposed by the Java API to fix code coverage
 */

#include <cvc5/cvc5_parser.h>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackUncovered : public TestApi
{
};

TEST_F(TestApiBlackUncovered, comparison_operators)
{
  cvc5::Result res;
  ASSERT_FALSE(res != res);
  cvc5::Sort sort;
  ASSERT_FALSE(sort != sort);
  ASSERT_TRUE(sort <= sort);
  ASSERT_TRUE(sort >= sort);
  ASSERT_FALSE(sort > sort);
  cvc5::Op op;
  ASSERT_FALSE(op != op);
  cvc5::Term term;
  ASSERT_FALSE(term != term);
  ASSERT_TRUE(term <= term);
  ASSERT_TRUE(term >= term);
  ASSERT_FALSE(term > term);
}

TEST_F(TestApiBlackUncovered, exception_getmessage)
{
  d_solver->setOption("produce-models", "true");
  Term x = d_tm.mkConst(d_tm.getBooleanSort(), "x");
  d_solver->assertFormula(x.eqTerm(x).notTerm());

  ASSERT_THROW(d_solver->getValue(x), CVC5ApiRecoverableException);

  try
  {
    d_solver->getValue(x);
  }
  catch (const CVC5ApiRecoverableException& e)
  {
    ASSERT_NO_THROW(e.getMessage());
  }
}

TEST_F(TestApiBlackUncovered, term_native_types)
{
  Term t = d_tm.mkInteger(0);
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
  Term t = d_tm.mkInteger(0);
  t = d_tm.mkTerm(Kind::GT, {t, t});
  Term::const_iterator it;
  it = t.begin();
  auto it2(it);
  ASSERT_FALSE(it == t.end());
  ASSERT_FALSE(it != it2);
  *it2;
  ++it;
  it++;
}

TEST_F(TestApiBlackUncovered, streaming_operators_to_string)
{
  std::stringstream ss;
  ss << cvc5::Kind::EQUAL << std::to_string(cvc5::Kind::EQUAL)
     << cvc5::kindToString(cvc5::Kind::EQUAL);
  ss << cvc5::SortKind::ARRAY_SORT << std::to_string(cvc5::SortKind::ARRAY_SORT)
     << cvc5::sortKindToString(cvc5::SortKind::ARRAY_SORT);
  ss << cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE
     << std::to_string(cvc5::RoundingMode::ROUND_TOWARD_NEGATIVE);
  ss << cvc5::UnknownExplanation::UNKNOWN_REASON
     << std::to_string(cvc5::UnknownExplanation::UNKNOWN_REASON);
  ss << cvc5::modes::BlockModelsMode::LITERALS
     << std::to_string(cvc5::modes::BlockModelsMode::LITERALS);
  ss << cvc5::modes::LearnedLitType::PREPROCESS
     << std::to_string(cvc5::modes::LearnedLitType::PREPROCESS);
  ss << cvc5::modes::ProofComponent::FULL
     << std::to_string(cvc5::modes::ProofComponent::FULL);
  ss << cvc5::modes::FindSynthTarget::ENUM
     << std::to_string(cvc5::modes::FindSynthTarget::ENUM);
  ss << cvc5::modes::InputLanguage::SMT_LIB_2_6
     << std::to_string(cvc5::modes::InputLanguage::SMT_LIB_2_6);
  ss << cvc5::modes::ProofFormat::LFSC
     << std::to_string(cvc5::modes::ProofFormat::LFSC);
  ss << cvc5::SkolemId::PURIFY << std::to_string(cvc5::SkolemId::PURIFY);
  ss << cvc5::ProofRule::ASSUME;
  ss << cvc5::Result();
  ss << cvc5::Op();
  ss << cvc5::SynthResult();
  ss << cvc5::Grammar();

  Sort intsort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(intsort, "x");

  ss << std::vector<Term>{x, x};
  ss << std::set<Term>{x, x};
  ss << std::unordered_set<Term>{x, x};
}

TEST_F(TestApiBlackUncovered, mkString)
{
  std::wstring s;
  ASSERT_EQ(d_tm.mkString(s).getStringValue(), s);
  ASSERT_EQ(d_solver->mkString(s).getStringValue(), s);
}

TEST_F(TestApiBlackUncovered, hash)
{
  std::hash<Op>()(Op());
  std::hash<Sort>()(Sort());
}

TEST_F(TestApiBlackUncovered, isOutputOn)
{
  d_solver->isOutputOn("inst");
  d_solver->getOutput("inst");
}

TEST_F(TestApiBlackUncovered, Options)
{
  auto dopts = d_solver->getDriverOptions();
  dopts.err();
  dopts.in();
  dopts.out();
}

TEST_F(TestApiBlackUncovered, Statistics)
{
  Stat stat;
  stat = Stat();
  Statistics stats = d_solver->getStatistics();
  auto it = stats.begin();
  it++;
  it--;
  ++it;
  --it;
  testing::internal::CaptureStdout();
  d_solver->printStatisticsSafe(STDOUT_FILENO);
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

  dtd = d_tm.mkDatatypeDecl("list");
  dtcd = d_tm.mkDatatypeConstructorDecl("cons");
  dtcd.addSelector("head", d_tm.getIntegerSort());
  dtd.addConstructor(dtcd);
  Sort s = d_tm.mkDatatypeSort(dtd);
  d = s.getDatatype();
  dc = d.getConstructor("cons");
  dc.getSelector("head");

  {
    Datatype::const_iterator it;
    it = d.begin();
    ASSERT_TRUE(it != d.end());
    *it;
    it->getName();
    ++it;
    ASSERT_TRUE(it == d.end());
    it++;
  }
  {
    DatatypeConstructor::const_iterator it;
    it = dc.begin();
    ASSERT_TRUE(it != dc.end());
    *it;
    it->getName();
    ++it;
    it = dc.begin();
    it++;
    ASSERT_TRUE(it == dc.end());
  }

  {
    std::stringstream ss;
    ss << d;
    ss << dtcd;
    ss << dc;
    ss << d.getSelector("head");
  }
}

TEST_F(TestApiBlackUncovered, Proof)
{
  Proof proof;
  ASSERT_EQ(proof.getRule(), ProofRule::UNKNOWN);
  ASSERT_EQ(std::hash<cvc5::ProofRule>()(ProofRule::UNKNOWN),
            static_cast<size_t>(ProofRule::UNKNOWN));
  ASSERT_TRUE(proof.getResult().isNull());
  ASSERT_TRUE(proof.getChildren().empty());
  ASSERT_TRUE(proof.getArguments().empty());
}

TEST_F(TestApiBlackUncovered, SkolemId)
{
  ASSERT_EQ(std::hash<cvc5::SkolemId>()(SkolemId::PURIFY),
            static_cast<size_t>(SkolemId::PURIFY));
}

TEST_F(TestApiBlackUncovered, Parser)
{
  parser::Command command;
  Solver solver;
  parser::InputParser inputParser(&solver);
  std::stringstream ss;
  ss << command << std::endl;
  inputParser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "Parser");
  parser::ParserException defaultConstructor;
  std::string message = "error";
  const char* cMessage = "error";
  std::string filename = "file.smt2";
  parser::ParserException stringConstructor(message);
  parser::ParserException cStringConstructor(cMessage);
  parser::ParserException exception(message, filename, 10, 11);
  exception.toStream(ss);
  ASSERT_EQ(message, exception.getMessage());
  ASSERT_EQ(message, exception.getMessage());
  ASSERT_EQ(filename, exception.getFilename());
  ASSERT_EQ(10, exception.getLine());
  ASSERT_EQ(11, exception.getColumn());

  parser::ParserEndOfFileException eofDefault;
  parser::ParserEndOfFileException eofString(message);
  parser::ParserEndOfFileException eofCMessage(cMessage);
  parser::ParserEndOfFileException eof(message, filename, 10, 11);
}

}  // namespace test
}  // namespace cvc5::internal
