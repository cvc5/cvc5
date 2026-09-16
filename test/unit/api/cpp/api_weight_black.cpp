/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SyGuS weight C++ API.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackWeight : public TestApi
{
 protected:
  void SetUp() override
  {
    TestApi::SetUp();
    d_solver->setOption("sygus", "true");
    d_solver->setLogic("NIA");
  }
};

TEST_F(TestApiBlackWeight, declareWeight)
{
  Weight w = d_solver->declareWeight("w");
  ASSERT_EQ(w.getName(), "w");
  // declared without :default, so the default value is 0.
  ASSERT_TRUE(w.getDefaultValue() == d_tm.mkInteger(0));
}

TEST_F(TestApiBlackWeight, declareWeightRequiresSygus)
{
  // Without the sygus option, declareWeight must fail.
  Solver s(d_tm);
  ASSERT_THROW(s.declareWeight("w"), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, declareWeightWithDefault)
{
  Term five = d_tm.mkInteger(5);
  Weight w = d_solver->declareWeight("w", five);
  ASSERT_EQ(w.getName(), "w");
  ASSERT_TRUE(w.getDefaultValue() == five);

  Term nullTerm;
  // The default must be a non-null integer constant.
  ASSERT_THROW(d_solver->declareWeight("bad", nullTerm), CVC5ApiException);
  ASSERT_THROW(d_solver->declareWeight("bad", d_tm.mkBoolean(true)),
               CVC5ApiException);
  ASSERT_THROW(d_solver->declareWeight("bad", d_tm.mkReal(1, 2)),
               CVC5ApiException);
  // An integer term that is not a value is rejected.
  ASSERT_THROW(d_solver->declareWeight("bad", d_tm.mkVar(d_int)),
               CVC5ApiException);

  // Still requires sygus.
  Solver s(d_tm);
  ASSERT_THROW(s.declareWeight("w", five), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, getDefaultValue)
{
  Term five = d_tm.mkInteger(5);
  Weight wDefault = d_solver->declareWeight("a", five);
  ASSERT_TRUE(wDefault.getDefaultValue() == five);
  // Weights declared without :default get 0.
  Weight wZero = d_solver->declareWeight("b");
  ASSERT_TRUE(wZero.getDefaultValue() == d_tm.mkInteger(0));
}

TEST_F(TestApiBlackWeight, equalHashOrder)
{
  Weight w1 = d_solver->declareWeight("a");
  Weight w2 = d_solver->declareWeight("b");

  ASSERT_TRUE(w1 == w1);
  ASSERT_FALSE(w1 == w2);
  ASSERT_TRUE(w1 != w2);
  ASSERT_FALSE(w1 != w1);

  // operator< is a strict order: irreflexive and asymmetric.
  ASSERT_FALSE(w1 < w1);
  ASSERT_NE(w1 < w2, w2 < w1);

  // Equal weights have equal hashes.
  ASSERT_EQ(std::hash<Weight>{}(w1), std::hash<Weight>{}(w1));

  // Weights from different term managers are not equal.
  TermManager tm2;
  Solver s2(tm2);
  s2.setOption("sygus", "true");
  Weight w3 = s2.declareWeight("a");
  ASSERT_FALSE(w1 == w3);
  ASSERT_TRUE(w1 != w3);

  // Weights are usable as keys of a WeightMap.
  WeightMap m;
  m[w1] = d_tm.mkInteger(1);
  m[w2] = d_tm.mkInteger(2);
  m[w1] = d_tm.mkInteger(3);
  ASSERT_EQ(m.size(), 2);
  ASSERT_TRUE(m[w1] == d_tm.mkInteger(3));
}

TEST_F(TestApiBlackWeight, mkWeightSymbol)
{
  Term x = d_tm.mkVar(d_int, "x");
  Term start = d_tm.mkVar(d_int, "Start");
  Weight w = d_solver->declareWeight("w");

  Grammar g = d_solver->mkGrammar({x}, {start});
  g.addRule(start, x);
  Term f = d_solver->synthFun("f", {x}, d_int, g);

  Term ws = d_solver->mkWeightSymbol(w, f);
  // The weight symbol has integer sort.
  ASSERT_EQ(ws.getSort(), d_int);

  Term nullTerm;
  ASSERT_THROW(d_solver->mkWeightSymbol(w, nullTerm), CVC5ApiException);

  // The weight must belong to this solver's term manager.
  TermManager tm2;
  Solver s2(tm2);
  s2.setOption("sygus", "true");
  Weight w2 = s2.declareWeight("w");
  ASSERT_THROW(d_solver->mkWeightSymbol(w2, f), CVC5ApiException);

  // mkWeightSymbol requires sygus mode.
  Solver s3(d_tm);
  ASSERT_THROW(s3.mkWeightSymbol(w, f), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, addRuleWithWeights)
{
  Term nullTerm;
  Term x = d_tm.mkVar(d_int, "x");
  Term start = d_tm.mkVar(d_int, "Start");
  Term nts = d_tm.mkVar(d_int, "nts");
  Weight w = d_solver->declareWeight("w");
  WeightMap weights{{w, d_tm.mkInteger(1)}};

  Grammar g = d_solver->mkGrammar({x}, {start});
  Term add = d_tm.mkTerm(Kind::ADD, {start, start});

  ASSERT_NO_THROW(g.addRule(start, add, weights));
  // An empty weight map keeps the legacy behavior.
  ASSERT_NO_THROW(g.addRule(start, x, {}));

  ASSERT_THROW(g.addRule(nullTerm, x, weights), CVC5ApiException);
  ASSERT_THROW(g.addRule(start, nullTerm, weights), CVC5ApiException);
  ASSERT_THROW(g.addRule(nts, x, weights), CVC5ApiException);
  // Rule must have a matching sort.
  ASSERT_THROW(g.addRule(start, d_tm.mkBoolean(true), weights),
               CVC5ApiException);

  // After the grammar is bound to a synth-fun, adding is rejected.
  d_solver->synthFun("f", {x}, d_int, g);
  ASSERT_THROW(g.addRule(start, x, weights), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, addRulesWithWeights)
{
  Term nullTerm;
  Term x = d_tm.mkVar(d_int, "x");
  Term start = d_tm.mkVar(d_int, "Start");
  Term nts = d_tm.mkVar(d_int, "nts");
  Weight w = d_solver->declareWeight("w");

  Grammar g = d_solver->mkGrammar({x}, {start});
  std::vector<Term> rules = {d_tm.mkInteger(0), d_tm.mkInteger(1), x};
  std::vector<WeightMap> weights = {
      {}, {{w, d_tm.mkInteger(1)}}, {{w, d_tm.mkInteger(2)}}};

  ASSERT_NO_THROW(g.addRules(start, rules, weights));
  // An empty weights vector keeps the legacy behavior.
  ASSERT_NO_THROW(g.addRules(start, {d_tm.mkInteger(3)}));

  ASSERT_THROW(g.addRules(nullTerm, rules, weights), CVC5ApiException);
  ASSERT_THROW(g.addRules(start, {nullTerm}, {{}}), CVC5ApiException);
  ASSERT_THROW(g.addRules(nts, rules, weights), CVC5ApiException);
  ASSERT_THROW(g.addRules(start, {d_tm.mkBoolean(true)}, {{}}),
               CVC5ApiException);

  d_solver->synthFun("f", {x}, d_int, g);
  ASSERT_THROW(g.addRules(start, rules, weights), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, addAnyConstantWithWeights)
{
  Term nullTerm;
  Term start = d_tm.mkVar(d_int, "Start");
  Term nts = d_tm.mkVar(d_int, "nts");
  Weight w = d_solver->declareWeight("w");
  WeightMap weights{{w, d_tm.mkInteger(3)}};

  Grammar g = d_solver->mkGrammar({}, {start});

  ASSERT_NO_THROW(g.addAnyConstant(start, weights));
  ASSERT_NO_THROW(g.addAnyConstant(start, {}));

  ASSERT_THROW(g.addAnyConstant(nullTerm, weights), CVC5ApiException);
  ASSERT_THROW(g.addAnyConstant(nts, weights), CVC5ApiException);

  d_solver->synthFun("f", {}, d_int, g);
  ASSERT_THROW(g.addAnyConstant(start, weights), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, addAnyVariableWithWeights)
{
  Term nullTerm;
  Term x = d_tm.mkVar(d_int, "x");
  Term start = d_tm.mkVar(d_int, "Start");
  Term nts = d_tm.mkVar(d_int, "nts");
  Weight w = d_solver->declareWeight("w");
  WeightMap weights{{w, d_tm.mkInteger(7)}};

  Grammar g = d_solver->mkGrammar({x}, {start});

  ASSERT_NO_THROW(g.addAnyVariable(start, weights));
  ASSERT_NO_THROW(g.addAnyVariable(start, {}));

  ASSERT_THROW(g.addAnyVariable(nullTerm, weights), CVC5ApiException);
  ASSERT_THROW(g.addAnyVariable(nts, weights), CVC5ApiException);

  d_solver->synthFun("f", {x}, d_int, g);
  ASSERT_THROW(g.addAnyVariable(start, weights), CVC5ApiException);
}

TEST_F(TestApiBlackWeight, synthesizeWithWeightConstraint)
{
  d_solver->setOption("incremental", "false");

  Term x = d_tm.mkVar(d_int, "x");
  Term start = d_tm.mkVar(d_int, "Start");
  Term add = d_tm.mkTerm(Kind::ADD, {start, start});
  Term mult = d_tm.mkTerm(Kind::MULT, {start, start});

  Weight w = d_solver->declareWeight("w");
  Grammar g = d_solver->mkGrammar({x}, {start});
  // Constants and the input variable have the default weight 0.
  g.addRules(start, {d_tm.mkInteger(0), d_tm.mkInteger(1), x});
  // `+` costs 1, `*` costs 31.
  g.addRule(start, add, {{w, d_tm.mkInteger(1)}});
  g.addRule(start, mult, {{w, d_tm.mkInteger(31)}});

  Term f = d_solver->synthFun("f", {x}, d_int, g);
  Term varX = d_solver->declareSygusVar("x", d_int);
  Term fX = d_tm.mkTerm(Kind::APPLY_UF, {f, varX});

  // (= (f x) (* 3 x))
  d_solver->addSygusConstraint(d_tm.mkTerm(
      Kind::EQUAL, {fX, d_tm.mkTerm(Kind::MULT, {d_tm.mkInteger(3), varX})}));
  // (= (_ w f) 2): a solution must use exactly two `+` applications.
  Term wF = d_solver->mkWeightSymbol(w, f);
  d_solver->addSygusConstraint(
      d_tm.mkTerm(Kind::EQUAL, {wF, d_tm.mkInteger(2)}));

  ASSERT_TRUE(d_solver->checkSynth().hasSolution());
  ASSERT_NO_THROW(d_solver->getSynthSolution(f));
}

}  // namespace test
}  // namespace cvc5::internal
