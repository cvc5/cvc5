/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr, Aina Niemetz, Mudathir Mohamed
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

#include <gtest/gtest.h>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackProof : public TestApi
{
 protected:
  Proof createProof()
  {
    d_solver->setOption("produce-proofs", "true");

    Sort uSort = d_tm.mkUninterpretedSort("u");
    Sort intSort = d_tm.getIntegerSort();
    Sort boolSort = d_tm.getBooleanSort();
    Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
    Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);
    std::vector<Proof> proof;

    Term x = d_tm.mkConst(uSort, "x");
    Term y = d_tm.mkConst(uSort, "y");
    Term f = d_tm.mkConst(uToIntSort, "f");
    Term p = d_tm.mkConst(intPredSort, "p");
    Term zero = d_tm.mkInteger(0);
    Term one = d_tm.mkInteger(1);
    Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
    Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
    Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
    Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
    Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});
    d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_x}));
    d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_y}));
    d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {sum, one}));
    d_solver->assertFormula(p_0);
    d_solver->assertFormula(p_f_y.notTerm());
    d_solver->checkSat();

    return d_solver->getProof().front();
  }

  Proof createRewriteProof()
  {
    d_solver->setOption("produce-proofs", "true");
    d_solver->setOption("proof-granularity", "dsl-rewrite");
    Sort intSort = d_tm.getIntegerSort();
    Term x = d_tm.mkConst(intSort, "x");
    Term twoX = d_tm.mkTerm(Kind::MULT, {d_tm.mkInteger(2), x});
    Term xPlusX = d_tm.mkTerm(Kind::ADD, {x, x});
    d_solver->assertFormula(d_tm.mkTerm(Kind::DISTINCT, {twoX, xPlusX}));
    d_solver->checkSat();
    return d_solver->getProof().front();
  }
};

TEST_F(TestApiBlackProof, nullProof)
{
  Proof proof;
  ASSERT_EQ(proof.getRule(), ProofRule::UNKNOWN);
  ASSERT_EQ(std::hash<cvc5::ProofRule>()(ProofRule::UNKNOWN),
            static_cast<size_t>(ProofRule::UNKNOWN));
  ASSERT_TRUE(proof.getResult().isNull());
  ASSERT_TRUE(proof.getChildren().empty());
  ASSERT_TRUE(proof.getArguments().empty());
}

TEST_F(TestApiBlackProof, getRule)
{
  Proof proof = createProof();
  ASSERT_EQ(proof.getRule(), ProofRule::SCOPE);
}

TEST_F(TestApiBlackProof, getRewriteRule)
{
  Proof proof = createRewriteProof();
  ASSERT_THROW(proof.getRewriteRule(), CVC5ApiException);
  ProofRule rule;
  std::vector<Proof> stack;
  stack.push_back(proof);
  do
  {
    proof = stack.back();
    stack.pop_back();
    rule = proof.getRule();
    std::vector<Proof> children = proof.getChildren();
    stack.insert(stack.cend(), children.cbegin(), children.cend());
  } while (rule != ProofRule::DSL_REWRITE);
  ASSERT_NO_THROW(proof.getRewriteRule());
}

TEST_F(TestApiBlackProof, getResult)
{
  Proof proof = createProof();
  ASSERT_NO_THROW(proof.getResult());
}

TEST_F(TestApiBlackProof, getChildren)
{
  Proof proof = createProof();
  std::vector<Proof> children;
  ASSERT_NO_THROW(children = proof.getChildren());
  ASSERT_FALSE(children.empty());
}

TEST_F(TestApiBlackProof, getArguments)
{
  Proof proof = createProof();
  ASSERT_NO_THROW(proof.getArguments());
}

TEST_F(TestApiBlackProof, equalhash)
{
  Proof x = createProof();
  Proof y = x.getChildren()[0];
  Proof z;

  ASSERT_TRUE(x == x);
  ASSERT_FALSE(x != x);
  ASSERT_FALSE(x == y);
  ASSERT_TRUE(x != y);
  ASSERT_FALSE(x == z);
  ASSERT_TRUE(x != z);

  ASSERT_TRUE(std::hash<Proof>()(x) == std::hash<Proof>()(x));
  (void)std::hash<Proof>{}(Proof());
  ASSERT_FALSE(std::hash<Proof>()(x) == std::hash<Proof>()(y));
}

}  // namespace test
}  // namespace cvc5::internal
