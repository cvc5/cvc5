/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Testing functions that are not exposed by the C API for code coverage.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackUncovered : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_solver.reset(new cvc5::Solver(d_tm));
    d_bool = d_tm.getBooleanSort();
    d_int = d_tm.getIntegerSort();
  }
  cvc5::TermManager d_tm;
  std::unique_ptr<cvc5::Solver> d_solver;
  cvc5::Sort d_bool;
  cvc5::Sort d_int;
};

TEST_F(TestCApiBlackUncovered, deprecated)
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
  (void)slv.mkString(s);
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
  (void)cvc5::parser::SymbolManager(&slv);
}

TEST_F(TestCApiBlackUncovered, stream_operators)
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
  ss << cvc5::modes::InputLanguage::SMT_LIB_2_6
     << std::to_string(cvc5::modes::InputLanguage::SMT_LIB_2_6);
  ss << cvc5::modes::ProofFormat::LFSC
     << std::to_string(cvc5::modes::ProofFormat::LFSC);
  ss << cvc5::ProofRule::ASSUME << std::to_string(cvc5::ProofRule::ASSUME);
  ss << cvc5::ProofRewriteRule::NONE
     << std::to_string(cvc5::ProofRewriteRule::NONE);
  ss << cvc5::SkolemId::PURIFY << std::to_string(cvc5::SkolemId::PURIFY);
  ss << d_tm.mkOp(Kind::BITVECTOR_EXTRACT, {4, 0});
  ss << d_tm.mkDatatypeConstructorDecl("cons");

  Sort intsort = d_tm.getIntegerSort();
  Term x = d_tm.mkConst(intsort, "x");

  ss << std::vector<Term>{x, x};
  ss << std::set<Term>{x, x};
  ss << std::unordered_set<Term>{x, x};

  d_solver->setOption("sygus", "true");
  (void)d_solver->synthFun("f", {}, d_bool);
  ss << d_solver->checkSynth();
  ss << d_solver->mkGrammar({}, {d_tm.mkVar(d_bool)});
  ss << d_solver->checkSat();

  DatatypeDecl decl = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_int);
  decl.addConstructor(cons);
  Datatype dt = d_tm.mkDatatypeSort(decl).getDatatype();
  ss << dt;
  DatatypeConstructor ctor = dt[0];
  ss << ctor;
  DatatypeSelector head = ctor.getSelector("head");
  ss << head;

  OptionInfo info = d_solver->getOptionInfo("verbose");
  ss << info;
}

TEST_F(TestCApiBlackUncovered, default_constructors)
{
  (void)cvc5::Op();
  (void)cvc5::Datatype();
  (void)cvc5::DatatypeDecl();
  (void)cvc5::DatatypeConstructorDecl();
  (void)cvc5::DatatypeConstructor();
  (void)cvc5::DatatypeSelector();
  (void)cvc5::SynthResult();
  (void)cvc5::Grammar();
  (void)cvc5::Result();
  (void)cvc5::Proof();
  (void)cvc5::parser::Command();
}

TEST_F(TestCApiBlackUncovered, comparison_operators)
{
  cvc5::Sort sort;
  ASSERT_TRUE(sort <= sort);
  ASSERT_TRUE(sort >= sort);
  cvc5::Term term;
  ASSERT_TRUE(term <= term);
  ASSERT_TRUE(term >= term);
}

TEST_F(TestCApiBlackUncovered, term_creation)
{
  d_tm.mkTrue().notTerm();
  d_tm.mkTrue().andTerm(d_tm.mkTrue());
  d_tm.mkTrue().orTerm(d_tm.mkTrue());
  d_tm.mkTrue().xorTerm(d_tm.mkTrue());
  d_tm.mkTrue().eqTerm(d_tm.mkTrue());
  d_tm.mkTrue().impTerm(d_tm.mkTrue());
  d_tm.mkTrue().iteTerm(d_tm.mkTrue(), d_tm.mkFalse());
}

TEST_F(TestCApiBlackUncovered, term_iterators)
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

TEST_F(TestCApiBlackUncovered, dt_iterators)
{
  // default constructors

  DatatypeDecl decl = d_tm.mkDatatypeDecl("list");
  DatatypeConstructorDecl cons = d_tm.mkDatatypeConstructorDecl("cons");
  cons.addSelector("head", d_int);
  decl.addConstructor(cons);
  Sort list = d_tm.mkDatatypeSort(decl);
  Datatype dt = list.getDatatype();
  DatatypeConstructor dt_cons = dt["cons"];
  DatatypeSelector dt_sel = dt_cons["head"];

  {
    Datatype::const_iterator it;
    it = dt.begin();
    ASSERT_TRUE(it != dt.end());
    *it;
    it->getName();
    ++it;
    ASSERT_TRUE(it == dt.end());
    it++;
  }
  {
    DatatypeConstructor::const_iterator it;
    it = dt_cons.begin();
    ASSERT_TRUE(it != dt_cons.end());
    *it;
    it->getName();
    ++it;
    it = dt_cons.begin();
    it++;
    ASSERT_TRUE(it == dt_cons.end());
  }
}

TEST_F(TestCApiBlackUncovered, stats_iterators)
{
  Stat stat;
  stat = Stat();
  Statistics stats = d_solver->getStatistics();
  auto it = stats.begin();
  it++;
  it--;
  ++it;
  --it;
  ASSERT_EQ(it, stats.begin());
  ASSERT_FALSE(stats.begin() == stats.end());
  ASSERT_TRUE(stats.begin() != stats.end());
  std::stringstream ss;
  ss << stats;
  ss << it->first;
}

TEST_F(TestCApiBlackUncovered, check_sat_assuming)
{
  d_solver->checkSatAssuming(d_tm.mkTrue());
}

TEST_F(TestCApiBlackUncovered, option_info)
{
  cvc5::OptionInfo info = d_solver->getOptionInfo("print-success");
  (void)info.boolValue();
  info = d_solver->getOptionInfo("verbosity");
  (void)info.intValue();
  info = d_solver->getOptionInfo("rlimit");
  (void)info.uintValue();
  info = d_solver->getOptionInfo("random-freq");
  (void)info.doubleValue();
  info = d_solver->getOptionInfo("force-logic");
  (void)info.stringValue();
}

class PluginListen : public Plugin
{
 public:
  PluginListen(TermManager& tm)
      : Plugin(tm), d_hasSeenTheoryLemma(false), d_hasSeenSatClause(false)
  {
  }
  virtual ~PluginListen() {}
  void notifySatClause(const Term& cl) override
  {
    Plugin::notifySatClause(cl);  // Cover default implementation
    d_hasSeenSatClause = true;
  }
  bool hasSeenSatClause() const { return d_hasSeenSatClause; }
  void notifyTheoryLemma(const Term& lem) override
  {
    Plugin::notifyTheoryLemma(lem);  // Cover default implementation
    d_hasSeenTheoryLemma = true;
  }
  bool hasSeenTheoryLemma() const { return d_hasSeenTheoryLemma; }
  std::string getName() override { return "PluginListen"; }

 private:
  /** have we seen a theory lemma? */
  bool d_hasSeenTheoryLemma;
  /** have we seen a SAT clause? */
  bool d_hasSeenSatClause;
};

TEST_F(TestCApiBlackUncovered, plugin_uncovered_default)
{
  // NOTE: this shouldn't be necessary but ensures notifySatClause is called
  // here.
  d_solver->setOption("plugin-notify-sat-clause-in-solve", "false");
  PluginListen pl(d_tm);
  d_solver->addPlugin(pl);
  Sort stringSort = d_tm.getStringSort();
  Term x = d_tm.mkConst(stringSort, "x");
  Term y = d_tm.mkConst(stringSort, "y");
  Term ctn1 = d_tm.mkTerm(Kind::STRING_CONTAINS, {x, y});
  Term ctn2 = d_tm.mkTerm(Kind::STRING_CONTAINS, {y, x});
  d_solver->assertFormula(d_tm.mkTerm(Kind::OR, {ctn1, ctn2}));
  Term lx = d_tm.mkTerm(Kind::STRING_LENGTH, {x});
  Term ly = d_tm.mkTerm(Kind::STRING_LENGTH, {y});
  Term lc = d_tm.mkTerm(Kind::GT, {lx, ly});
  d_solver->assertFormula(lc);
  ASSERT_TRUE(d_solver->checkSat().isSat());
  // above input formulas should induce a theory lemma and SAT clause learning
  ASSERT_TRUE(pl.hasSeenTheoryLemma());
  ASSERT_TRUE(pl.hasSeenSatClause());
}

TEST_F(TestCApiBlackUncovered, parser)
{
  parser::Command command;
  Solver solver(d_tm);
  parser::InputParser parser(&solver);
  (void)parser.getSolver();
  std::stringstream ss;
  ss << command << std::endl;
  parser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "Parser");
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

TEST_F(TestCApiBlackUncovered, driver_options)
{
  auto dopts = d_solver->getDriverOptions();
  dopts.err();
  dopts.in();
  dopts.out();
}

}  // namespace cvc5::internal::test
