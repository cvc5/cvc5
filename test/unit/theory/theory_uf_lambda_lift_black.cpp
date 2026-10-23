/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tests for lambda lifting proofs and preprocessing.
 */

#include "expr/function_array_const.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "test_smt.h"
#include "theory/uf/function_const.h"
#include "theory/uf/lambda_lift.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestTheoryBlackUfLambdaLift : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setLogic(std::string("HO_ALL"));
    d_slvEngine->setOption("produce-proofs", "true");
    d_slvEngine->setOption("proof-check", "eager");
    d_slvEngine->finishInit();
  }

  void checkProof(const TrustNode& tn)
  {
    ASSERT_NE(tn.getGenerator(), nullptr);
    std::shared_ptr<ProofNode> pf =
        tn.getGenerator()->getProofFor(tn.getProven());
    ASSERT_NE(pf, nullptr);
    ASSERT_EQ(pf->getResult(), tn.getProven());
    ASSERT_TRUE(pf->isClosed());
    std::vector<std::shared_ptr<ProofNode>> trusted;
    expr::getSubproofRule(pf, ProofRule::TRUST, trusted);
    ASSERT_TRUE(trusted.empty());
  }
};

TEST_F(TestTheoryBlackUfLambdaLift, lazy_lift_proofs)
{
  NodeManager* nm = d_nodeManager.get();
  theory::uf::LambdaLift ll(d_slvEngine->getEnv());
  TypeNode intType = nm->integerType();
  Node f = nm->mkDummySkolem("f", nm->mkFunctionType({intType}, intType));
  Node g =
      nm->mkDummySkolem("g", nm->mkFunctionType({intType, intType}, intType));
  Node zero = nm->mkConstInt(Rational(0));
  Node partial = nm->mkNode(Kind::HO_APPLY, g, zero);
  // Circular lambdas, including a partial application and a binary function.
  for (const Node& fun : {f, partial, g})
  {
    std::vector<Node> vars;
    std::vector<Node> app{fun};
    for (const TypeNode& type : fun.getType().getArgTypes())
    {
      Node v = nm->mkBoundVar(type);
      vars.push_back(v);
      app.push_back(v);
    }
    Node body = nm->mkNode(Kind::ADD,
                           nm->mkNode(Kind::APPLY_UF, app),
                           nm->mkConstInt(Rational(1)));
    Node lam =
        nm->mkNode(Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, vars), body);
    checkProof(ll.getLiftLemma(fun, lam));
  }
  Node x = nm->mkBoundVar(intType);
  Node lam =
      nm->mkNode(Kind::LAMBDA, nm->mkNode(Kind::BOUND_VAR_LIST, x), zero);
  Node array = theory::uf::FunctionConst::toArrayConst(lam);
  ASSERT_FALSE(array.isNull());
  Node fc = nm->mkConst(FunctionArrayConst(f.getType(), array));
  checkProof(ll.getLiftLemma(f, fc));
}

TEST_F(TestTheoryBlackUfLambdaLift, argument_equality_backtracking)
{
  NodeManager* nm = d_nodeManager.get();
  Env& env = d_slvEngine->getEnv();
  theory::uf::LambdaLift ll(env);
  TypeNode intType = nm->integerType();
  Node g =
      nm->mkDummySkolem("g", nm->mkFunctionType({intType, intType}, intType));
  Node x = nm->mkBoundVar(intType);
  Node lam = nm->mkNode(Kind::LAMBDA,
                        nm->mkNode(Kind::BOUND_VAR_LIST, x),
                        nm->mkNode(Kind::APPLY_UF, g, x, x));
  Node p = nm->mkDummySkolem(
      "p", nm->mkFunctionType({lam.getType()}, nm->booleanType()));
  Node app = nm->mkNode(Kind::APPLY_UF, p, lam);
  Node skolem = SkolemManager::mkPurifySkolem(lam);
  // Popping the user context must allow the equality to be emitted again.
  for (size_t i = 0; i < 2; ++i)
  {
    env.getUserContext()->push();
    std::vector<theory::SkolemLemma> lemmas;
    checkProof(ll.ppRewrite(app, lemmas));
    bool foundEquality = false;
    for (const theory::SkolemLemma& lemma : lemmas)
    {
      checkProof(lemma.d_lemma);
      foundEquality |= lemma.getProven() == skolem.eqNode(lam);
    }
    ASSERT_TRUE(foundEquality);
    lemmas.clear();
    ll.ppRewrite(app, lemmas);
    ASSERT_TRUE(lemmas.empty());
    env.getUserContext()->pop();
  }
}

}  // namespace test
}  // namespace cvc5::internal
