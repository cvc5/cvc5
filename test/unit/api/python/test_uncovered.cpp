/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Testing functions that are not exposed by the Python API for code coverage.
 */

#include <cvc5/cvc5_parser.h>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackUncovered : public TestApi
{
};

TEST_F(TestApiBlackUncovered, deprecated)
{
  std::stringstream ss;
  ss << cvc5::Kind::EQUAL << cvc5::kindToString(cvc5::Kind::EQUAL);
  ss << cvc5::SortKind::ARRAY_SORT
     << cvc5::sortKindToString(cvc5::SortKind::ARRAY_SORT);

  Solver slv;
  (void)slv.getBooleanSort();
  (void)slv.getIntegerSort();
  (void)slv.getRealSort();
  (void)slv.getRegExpSort();
  (void)slv.getRoundingModeSort();
  (void)slv.getStringSort();
  (void)slv.mkArraySort(slv.getBooleanSort(), slv.getIntegerSort());
  (void)slv.mkBitVectorSort(32);
  (void)slv.mkFloatingPointSort(5, 11);
  (void)slv.mkFiniteFieldSort("37");

  {
    DatatypeDecl decl = slv.mkDatatypeDecl("list");
    DatatypeConstructorDecl cons = slv.mkDatatypeConstructorDecl("cons");
    cons.addSelector("head", slv.getIntegerSort());
    decl.addConstructor(cons);
    decl.addConstructor(slv.mkDatatypeConstructorDecl("nil"));
    (void)slv.mkDatatypeSort(decl);
  }
  {
    DatatypeDecl decl1 = slv.mkDatatypeDecl("list1");
    DatatypeConstructorDecl cons1 = slv.mkDatatypeConstructorDecl("cons1");
    cons1.addSelector("head1", slv.getIntegerSort());
    decl1.addConstructor(cons1);
    DatatypeConstructorDecl nil1 = slv.mkDatatypeConstructorDecl("nil1");
    decl1.addConstructor(nil1);
    DatatypeDecl decl2 = slv.mkDatatypeDecl("list2");
    DatatypeConstructorDecl cons2 = slv.mkDatatypeConstructorDecl("cons2");
    cons2.addSelector("head2", slv.getIntegerSort());
    decl2.addConstructor(cons2);
    DatatypeConstructorDecl nil2 = slv.mkDatatypeConstructorDecl("nil2");
    decl2.addConstructor(nil2);
    std::vector<DatatypeDecl> decls = {decl1, decl2};
    ASSERT_NO_THROW(slv.mkDatatypeSorts(decls));
  }

  (void)slv.mkFunctionSort({slv.mkUninterpretedSort("u")},
                           slv.getIntegerSort());
  (void)slv.mkParamSort("T");
  (void)slv.mkPredicateSort({slv.getIntegerSort()});

  (void)slv.mkRecordSort({std::make_pair("b", slv.getBooleanSort()),
                          std::make_pair("bv", slv.mkBitVectorSort(8)),
                          std::make_pair("i", slv.getIntegerSort())});
  (void)slv.mkSetSort(slv.getBooleanSort());
  (void)slv.mkBagSort(slv.getBooleanSort());
  (void)slv.mkSequenceSort(slv.getBooleanSort());
  (void)slv.mkAbstractSort(SortKind::ARRAY_SORT);
  (void)slv.mkUninterpretedSort("u");
  (void)slv.mkUnresolvedDatatypeSort("u");
  (void)slv.mkUninterpretedSortConstructorSort(2, "s");
  (void)slv.mkTupleSort({slv.getIntegerSort()});
  (void)slv.mkNullableSort({slv.getIntegerSort()});
  (void)slv.mkTerm(Kind::STRING_IN_REGEXP,
                   {slv.mkConst(slv.getStringSort(), "s"), slv.mkRegexpAll()});
  (void)slv.mkTerm(slv.mkOp(Kind::REGEXP_ALLCHAR));
  (void)slv.mkTuple({slv.mkBitVector(3, "101", 2)});
  (void)slv.mkNullableSome(slv.mkBitVector(3, "101", 2));
  (void)slv.mkNullableVal(slv.mkNullableSome(slv.mkInteger(5)));
  (void)slv.mkNullableNull(slv.mkNullableSort(slv.getBooleanSort()));
  (void)slv.mkNullableIsNull(slv.mkNullableSome(slv.mkInteger(5)));
  (void)slv.mkNullableIsSome(slv.mkNullableSome(slv.mkInteger(5)));
  (void)slv.mkNullableSort(slv.getBooleanSort());
  (void)slv.mkNullableLift(Kind::ADD,
                           {slv.mkNullableSome(slv.mkInteger(1)),
                            slv.mkNullableSome(slv.mkInteger(2))});
  (void)slv.mkOp(Kind::DIVISIBLE, "2147483648");
  (void)slv.mkOp(Kind::TUPLE_PROJECT, {1, 2, 2});

  (void)slv.mkTrue();
  (void)slv.mkFalse();
  (void)slv.mkBoolean(true);
  (void)slv.mkPi();
  (void)slv.mkInteger("2");
  (void)slv.mkInteger(2);
  (void)slv.mkReal("2.1");
  (void)slv.mkReal(2);
  (void)slv.mkReal(2, 3);
  (void)slv.mkRegexpAll();
  (void)slv.mkRegexpAllchar();
  (void)slv.mkRegexpNone();
  (void)slv.mkEmptySet(slv.mkSetSort(slv.getIntegerSort()));
  (void)slv.mkEmptyBag(slv.mkBagSort(slv.getIntegerSort()));
  (void)slv.mkSepEmp();
  (void)slv.mkSepNil(slv.getIntegerSort());
  (void)slv.mkString("asdfasdf");
  std::wstring s;
  (void)slv.mkString(s).getStringValue();
  (void)slv.mkEmptySequence(slv.getIntegerSort());
  (void)slv.mkUniverseSet(slv.getIntegerSort());
  (void)slv.mkBitVector(32, 2);
  (void)slv.mkBitVector(32, "2", 10);
  (void)slv.mkFiniteFieldElem("0", slv.mkFiniteFieldSort("7"));
  (void)slv.mkConstArray(
      slv.mkArraySort(slv.getIntegerSort(), slv.getIntegerSort()),
      slv.mkInteger(2));
  (void)slv.mkFloatingPointPosInf(5, 11);
  (void)slv.mkFloatingPointNegInf(5, 11);
  (void)slv.mkFloatingPointNaN(5, 11);
  (void)slv.mkFloatingPointPosZero(5, 11);
  (void)slv.mkFloatingPointNegZero(5, 11);
  (void)slv.mkRoundingMode(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN);
  (void)slv.mkFloatingPoint(5, 11, slv.mkBitVector(16));
  (void)slv.mkFloatingPoint(
      slv.mkBitVector(1), slv.mkBitVector(5), slv.mkBitVector(10));
  (void)slv.mkCardinalityConstraint(slv.mkUninterpretedSort("u"), 3);

  (void)slv.mkVar(slv.getIntegerSort());
  (void)slv.mkDatatypeDecl("paramlist", {slv.mkParamSort("T")});

  (void)parser::SymbolManager(d_solver.get());
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

TEST_F(TestApiBlackUncovered, equalHash)
{
  DatatypeDecl decl1 = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons1 = d_tm.mkDatatypeConstructorDecl("cons");
  cons1.addSelector("head", d_tm.getIntegerSort());
  decl1.addConstructor(cons1);
  DatatypeConstructorDecl nil1 = d_tm.mkDatatypeConstructorDecl("nil");
  decl1.addConstructor(nil1);
  Sort list1 = d_tm.mkDatatypeSort(decl1);
  Datatype dt1 = list1.getDatatype();
  DatatypeConstructor consConstr1 = dt1[0];
  DatatypeConstructor nilConstr1 = dt1[1];
  DatatypeSelector head1 = consConstr1.getSelector("head");

  DatatypeDecl decl2 = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons2 = d_tm.mkDatatypeConstructorDecl("cons");
  cons2.addSelector("head", d_tm.getIntegerSort());
  decl2.addConstructor(cons2);
  DatatypeConstructorDecl nil2 = d_tm.mkDatatypeConstructorDecl("nil");
  decl2.addConstructor(nil2);
  Sort list2 = d_tm.mkDatatypeSort(decl2);
  Datatype dt2 = list2.getDatatype();
  DatatypeConstructor consConstr2 = dt2[0];
  DatatypeConstructor nilConstr2 = dt2[1];
  DatatypeSelector head2 = consConstr2.getSelector("head");

  ASSERT_EQ(decl1, decl1);
  ASSERT_FALSE(decl1 == decl2);
  ASSERT_EQ(cons1, cons1);
  ASSERT_FALSE(cons1 == cons2);
  ASSERT_EQ(nil1, nil1);
  ASSERT_FALSE(nil1 == nil2);
  ASSERT_EQ(consConstr1, consConstr1);
  ASSERT_FALSE(consConstr1 == consConstr2);
  ASSERT_EQ(head1, head1);
  ASSERT_FALSE(head1 == head2);
  ASSERT_EQ(dt1, dt1);
  ASSERT_FALSE(dt1 == dt2);

  ASSERT_EQ(std::hash<DatatypeDecl>{}(decl1), std::hash<DatatypeDecl>{}(decl1));
  ASSERT_EQ(std::hash<DatatypeDecl>{}(decl1), std::hash<DatatypeDecl>{}(decl2));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(cons1),
            std::hash<DatatypeConstructorDecl>{}(cons1));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(cons1),
            std::hash<DatatypeConstructorDecl>{}(cons2));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(nil1),
            std::hash<DatatypeConstructorDecl>{}(nil1));
  ASSERT_EQ(std::hash<DatatypeConstructorDecl>{}(nil1),
            std::hash<DatatypeConstructorDecl>{}(nil2));
  ASSERT_EQ(std::hash<DatatypeConstructor>{}(consConstr1),
            std::hash<DatatypeConstructor>{}(consConstr1));
  ASSERT_EQ(std::hash<DatatypeConstructor>{}(consConstr1),
            std::hash<DatatypeConstructor>{}(consConstr2));
  ASSERT_EQ(std::hash<DatatypeSelector>{}(head1),
            std::hash<DatatypeSelector>{}(head1));
  ASSERT_EQ(std::hash<DatatypeSelector>{}(head1),
            std::hash<DatatypeSelector>{}(head2));
  ASSERT_EQ(std::hash<Datatype>{}(dt1), std::hash<Datatype>{}(dt1));
  ASSERT_EQ(std::hash<Datatype>{}(dt1), std::hash<Datatype>{}(dt2));

  (void)std::hash<cvc5::Result>{}(cvc5::Result());
}

TEST_F(TestApiBlackUncovered, streaming_operators_to_string)
{
  std::stringstream ss;
  ss << cvc5::Kind::EQUAL << std::to_string(cvc5::Kind::EQUAL);
  ss << cvc5::SortKind::ARRAY_SORT
     << std::to_string(cvc5::SortKind::ARRAY_SORT);
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
  ss << cvc5::modes::OptionCategory::EXPERT
     << std::to_string(cvc5::modes::OptionCategory::EXPERT);
  ss << cvc5::modes::InputLanguage::SMT_LIB_2_6
     << std::to_string(cvc5::modes::InputLanguage::SMT_LIB_2_6);
  ss << cvc5::modes::ProofFormat::LFSC
     << std::to_string(cvc5::modes::ProofFormat::LFSC);
  ss << cvc5::ProofRule::ASSUME << std::to_string(cvc5::ProofRule::ASSUME);
  ss << cvc5::ProofRewriteRule::NONE
     << std::to_string(cvc5::ProofRewriteRule::NONE);
  ss << cvc5::SkolemId::PURIFY << std::to_string(cvc5::SkolemId::PURIFY);
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

TEST_F(TestApiBlackUncovered, grammar)
{
  d_solver->setOption("sygus", "true");

  Term x = d_tm.mkVar(d_bool, "x");
  Term start1 = d_tm.mkVar(d_bool, "start");
  Term start2 = d_tm.mkVar(d_bool, "start");
  Grammar g1 = d_solver->mkGrammar({}, {start1});
  ASSERT_EQ(g1, g1);
  ASSERT_FALSE(g1 != g1);
  ASSERT_EQ(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g1));
}

TEST_F(TestApiBlackUncovered, datatypeApi)
{
  DatatypeDecl dtypeSpec = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_tm.getIntegerSort());
  dtypeSpec.addConstructor(cons);
  DatatypeConstructorDecl nil = d_tm.mkDatatypeConstructorDecl("nil");
  dtypeSpec.addConstructor(nil);
  Sort listSort = d_tm.mkDatatypeSort(dtypeSpec);
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
  Term t = d_tm.mkInteger(0);
  d_tm.mkReal(0);
  d_tm.mkReal(0, 1);
  d_solver->mkReal(0);
  d_solver->mkReal(0, 1);
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
  Term t = d_tm.mkInteger(0);
  auto it = t.begin();
  auto it2(it);
  it++;
}

TEST_F(TestApiBlackUncovered, checkSatAssumingSingle)
{
  Sort boolsort = d_tm.getBooleanSort();
  Term b = d_tm.mkConst(boolsort, "b");
  d_solver->checkSatAssuming(b);
}

TEST_F(TestApiBlackUncovered, mkOpInitializerList)
{
  d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {1, 1});
  d_solver->mkOp(Kind::BITVECTOR_EXTRACT, {1, 1});
}

TEST_F(TestApiBlackUncovered, mkTermKind)
{
  Term b = d_tm.mkConst(d_tm.getRealSort(), "b");
  d_tm.mkTerm(Kind::GT, {b, b});
  d_solver->mkTerm(Kind::GT, {b, b});
}

TEST_F(TestApiBlackUncovered, getValue)
{
  d_solver->setOption("produce-models", "true");
  Sort boolsort = d_tm.getBooleanSort();
  Term b = d_tm.mkConst(boolsort, "b");
  d_solver->assertFormula(b);
  d_solver->checkSat();
  d_solver->getValue({b, b, b});
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

  std::stringstream ss;
  {
    auto info = d_solver->getOptionInfo("verbose");
    ss << info;
    }
    {
    auto info = d_solver->getOptionInfo("print-success");
    ss << info;
    info.boolValue();
    }
    {
    auto info = d_solver->getOptionInfo("verbosity");
    ss << info;
    info.intValue();
    }
    {
    auto info = d_solver->getOptionInfo("rlimit");
    ss << info;
    info.uintValue();
    }
    {
    auto info = d_solver->getOptionInfo("random-freq");
    ss << info;
    info.doubleValue();
    }
    {
    auto info = d_solver->getOptionInfo("force-logic");
    ss << info;
    info.stringValue();
    }
    {
    auto info = d_solver->getOptionInfo("simplification");
    ss << info;
    }
}

TEST_F(TestApiBlackUncovered, Statistics)
{
    d_solver->assertFormula(d_tm.mkConst(d_tm.getBooleanSort(), "x"));
    d_solver->checkSat();
    Statistics stats = d_solver->getStatistics();
    auto s = stats.get("global::totalTime");
    std::stringstream ss;
    ss << stats << s.toString();
    auto it = stats.begin();
    ASSERT_NE(it, stats.end());
    it++;
    it--;
    ++it;
    --it;
    ASSERT_EQ(it, stats.begin());
    ss << it->first;

    testing::internal::CaptureStdout();
    d_solver->printStatisticsSafe(STDOUT_FILENO);
    d_tm.printStatisticsSafe(STDOUT_FILENO);
    testing::internal::GetCapturedStdout();
}

TEST_F(TestApiBlackUncovered, SynthResult)
{
  d_solver->setOption("sygus", "true");
  (void)d_solver->synthFun("f", {}, d_bool);
  Term tfalse = d_tm.mkFalse();
  Term ttrue = d_tm.mkTrue();
  d_solver->addSygusConstraint(ttrue);
  cvc5::SynthResult res1 = d_solver->checkSynth();
  d_solver->addSygusConstraint(tfalse);
  cvc5::SynthResult res2 = d_solver->checkSynth();
  ASSERT_EQ(std::hash<cvc5::SynthResult>{}(res1),
            std::hash<cvc5::SynthResult>{}(res1));
}

// Copied from api/cpp/solver_black.cpp
TEST_F(TestApiBlackUncovered, declareOracleFunUnsat)
{
    d_solver->setOption("oracles", "true");
    Sort iSort = d_tm.getIntegerSort();
    // f is the function implementing (lambda ((x Int)) (+ x 1))
    Term f = d_solver->declareOracleFun(
        "f", {iSort}, iSort, [&](const std::vector<Term>& input) {
          if (input[0].isUInt32Value())
          {
            return d_tm.mkInteger(input[0].getUInt32Value() + 1);
          }
          return d_tm.mkInteger(0);
        });
    Term three = d_tm.mkInteger(3);
    Term five = d_tm.mkInteger(5);
    Term eq = d_tm.mkTerm(Kind::EQUAL,
                          {d_tm.mkTerm(Kind::APPLY_UF, {f, three}), five});
    d_solver->assertFormula(eq);
    d_solver->checkSat();
}

TEST_F(TestApiBlackUncovered, Proof)
{
  Proof proof;
  ASSERT_EQ(proof.getRule(), ProofRule::UNKNOWN);
  ASSERT_TRUE(proof.getResult().isNull());
  ASSERT_TRUE(proof.getChildren().empty());
  ASSERT_TRUE(proof.getArguments().empty());
}

TEST_F(TestApiBlackUncovered, ProofRewriteRule)
{
  ASSERT_EQ(std::hash<cvc5::ProofRewriteRule>()(ProofRewriteRule::NONE),
            static_cast<size_t>(ProofRewriteRule::NONE));
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
  ASSERT_EQ(inputParser.getSolver(), &solver);
  parser::SymbolManager* sm = inputParser.getSymbolManager();
  ASSERT_EQ(sm->isLogicSet(), false);
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
