/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the C++ API functions.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackGrammar : public TestApi
{
 protected:
  void SetUp() override
  {
    TestApi::SetUp();
    d_bool = d_tm.getBooleanSort();
  }
  Sort d_bool;
};

TEST_F(TestApiBlackGrammar, toString)
{
  d_solver->setOption("sygus", "true");
  Term start = d_tm.mkVar(d_bool);
  Grammar g = d_solver->mkGrammar({}, {start});
  ASSERT_EQ(g.toString(), "");
  g.addRule(start, d_tm.mkBoolean(false));
  ASSERT_NE(g.toString(), "");
  {
    std::stringstream ss;
    ss << g;
    ASSERT_EQ(ss.str(), g.toString());
  }
}

TEST_F(TestApiBlackGrammar, addRule)
{
  d_solver->setOption("sygus", "true");

  Term nullTerm;
  Term start = d_tm.mkVar(d_bool);
  Term nts = d_tm.mkVar(d_bool);

  Grammar g = d_solver->mkGrammar({}, {start});

  ASSERT_NO_THROW(g.addRule(start, d_tm.mkBoolean(false)));

  ASSERT_THROW(g.addRule(nullTerm, d_tm.mkBoolean(false)), CVC5ApiException);
  ASSERT_THROW(g.addRule(start, nullTerm), CVC5ApiException);
  ASSERT_THROW(g.addRule(nts, d_tm.mkBoolean(false)), CVC5ApiException);
  ASSERT_THROW(g.addRule(start, d_tm.mkInteger(0)), CVC5ApiException);

  d_solver->synthFun("f", {}, d_bool, g);

  ASSERT_THROW(g.addRule(start, d_tm.mkBoolean(false)), CVC5ApiException);
}

TEST_F(TestApiBlackGrammar, addRules)
{
  d_solver->setOption("sygus", "true");

  Term nullTerm;
  Term start = d_tm.mkVar(d_bool);
  Term nts = d_tm.mkVar(d_bool);

  Grammar g = d_solver->mkGrammar({}, {start});

  ASSERT_NO_THROW(g.addRules(start, {d_tm.mkBoolean(false)}));

  ASSERT_THROW(g.addRules(nullTerm, {d_tm.mkBoolean(false)}), CVC5ApiException);
  ASSERT_THROW(g.addRules(start, {nullTerm}), CVC5ApiException);
  ASSERT_THROW(g.addRules(nts, {d_tm.mkBoolean(false)}), CVC5ApiException);
  ASSERT_THROW(g.addRules(start, {d_tm.mkInteger(0)}), CVC5ApiException);

  d_solver->synthFun("f", {}, d_bool, g);

  ASSERT_THROW(g.addRules(start, {d_tm.mkBoolean(false)}), CVC5ApiException);
}

TEST_F(TestApiBlackGrammar, addAnyConstant)
{
  d_solver->setOption("sygus", "true");

  Term nullTerm;
  Term start = d_tm.mkVar(d_bool);
  Term nts = d_tm.mkVar(d_bool);

  Grammar g = d_solver->mkGrammar({}, {start});

  ASSERT_NO_THROW(g.addAnyConstant(start));
  ASSERT_NO_THROW(g.addAnyConstant(start));

  ASSERT_THROW(g.addAnyConstant(nullTerm), CVC5ApiException);
  ASSERT_THROW(g.addAnyConstant(nts), CVC5ApiException);

  d_solver->synthFun("f", {}, d_bool, g);

  ASSERT_THROW(g.addAnyConstant(start), CVC5ApiException);
}

TEST_F(TestApiBlackGrammar, addAnyVariable)
{
  d_solver->setOption("sygus", "true");

  Term nullTerm;
  Term x = d_tm.mkVar(d_bool);
  Term start = d_tm.mkVar(d_bool);
  Term nts = d_tm.mkVar(d_bool);

  Grammar g1 = d_solver->mkGrammar({x}, {start});
  Grammar g2 = d_solver->mkGrammar({}, {start});

  ASSERT_NO_THROW(g1.addAnyVariable(start));
  ASSERT_NO_THROW(g1.addAnyVariable(start));
  ASSERT_NO_THROW(g2.addAnyVariable(start));

  ASSERT_THROW(g1.addAnyVariable(nullTerm), CVC5ApiException);
  ASSERT_THROW(g1.addAnyVariable(nts), CVC5ApiException);

  d_solver->synthFun("f", {}, d_bool, g1);

  ASSERT_THROW(g1.addAnyVariable(start), CVC5ApiException);
}

TEST_F(TestApiBlackGrammar, equalHash)
{
  d_solver->setOption("sygus", "true");

  Term x = d_tm.mkVar(d_bool, "x");
  Term start1 = d_tm.mkVar(d_bool, "start");
  Term start2 = d_tm.mkVar(d_bool, "start");
  Grammar g1, g2;
  ASSERT_EQ(g1, g2);

  {
    g1 = d_solver->mkGrammar({}, {start1});
    g2 = d_solver->mkGrammar({}, {start1});
    ASSERT_EQ(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g1));
    ASSERT_EQ(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }

  {
    g1 = d_solver->mkGrammar({}, {start1});
    g2 = d_solver->mkGrammar({x}, {start1});
    ASSERT_NE(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }

  {
    g1 = d_solver->mkGrammar({x}, {start1});
    g2 = d_solver->mkGrammar({x}, {start2});
    ASSERT_NE(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }

  {
    g1 = d_solver->mkGrammar({x}, {start1});
    g2 = d_solver->mkGrammar({x}, {start1});
    g2.addAnyVariable(start1);
    ASSERT_NE(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }

  {
    g1 = d_solver->mkGrammar({x}, {start1});
    g2 = d_solver->mkGrammar({x}, {start1});
    std::vector<Term> rules = {d_tm.mkFalse()};
    g1.addRules(start1, rules);
    g2.addRules(start1, rules);
    ASSERT_EQ(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }

  {
    g1 = d_solver->mkGrammar({x}, {start1});
    g2 = d_solver->mkGrammar({x}, {start1});
    std::vector<Term> rules2 = {d_tm.mkFalse()};
    g2.addRules(start1, rules2);
    ASSERT_NE(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }

  {
    g1 = d_solver->mkGrammar({x}, {start1});
    g2 = d_solver->mkGrammar({x}, {start1});
    std::vector<Term> rules1 = {d_tm.mkTrue()};
    std::vector<Term> rules2 = {d_tm.mkFalse()};
    g1.addRules(start1, rules1);
    g2.addRules(start1, rules2);
    ASSERT_NE(std::hash<Grammar>{}(g1), std::hash<Grammar>{}(g2));
    ASSERT_EQ(g1, g1);
    ASSERT_NE(g1, g2);
  }
  (void)std::hash<Grammar>{}(Grammar());
}
}  // namespace test
}  // namespace cvc5::internal
