/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the core rewriter.
 */

#include "test_smt.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

using namespace theory;

class TestTheoryWhiteRewriter : public TestSmt
{
};

TEST_F(TestTheoryWhiteRewriter, deepFullRewrite)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode setType = d_nodeManager->mkSetType(intType);
  Node x = d_skolemManager->mkDummySkolem("x", intType);
  Node tail = d_skolemManager->mkDummySkolem("tail", setType);
  Node set = tail;

  constexpr size_t kDepth = 4000;
  for (size_t i = 0; i < kDepth; ++i)
  {
    Node elem = d_nodeManager->mkConstInt(Rational(i));
    Node singleton = d_nodeManager->mkNode(Kind::SET_SINGLETON, elem);
    set = d_nodeManager->mkNode(Kind::SET_UNION, singleton, set);
  }

  Node mem = d_nodeManager->mkNode(Kind::SET_MEMBER, x, set);
  Node rewritten = rr->rewrite(mem);

  ASSERT_EQ(rewritten.getKind(), Kind::OR);
  ASSERT_EQ(rewritten.getNumChildren(), kDepth + 1);

  Node memberTail = d_nodeManager->mkNode(Kind::SET_MEMBER, x, tail);
  bool foundTail = false;
  for (const Node& c : rewritten)
  {
    if (c == memberTail)
    {
      foundTail = true;
      break;
    }
  }
  ASSERT_TRUE(foundTail);
}

TEST_F(TestTheoryWhiteRewriter, macroDefinitionScope)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode intType = d_nodeManager->integerType();
  TypeNode predType =
      d_nodeManager->mkFunctionType(intType, d_nodeManager->booleanType());
  Node p = d_skolemManager->mkDummySkolem("p", predType);
  Node x = d_nodeManager->mkBoundVar("x", intType);
  Node y = d_nodeManager->mkBoundVar("y", intType);
  Node bvl = d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, x);
  Node px = d_nodeManager->mkNode(Kind::APPLY_UF, p, x);
  Node py = d_nodeManager->mkNode(Kind::APPLY_UF, p, y);
  Node closed = d_nodeManager->mkNode(Kind::FORALL, bvl, px);
  Node open = d_nodeManager->mkNode(Kind::FORALL, bvl, py);
  // forall x. p(x) defines p; forall x. p(y) does not define p on all inputs.
  ASSERT_FALSE(
      rr->rewriteViaRule(ProofRewriteRule::MACRO_QUANT_MACRO_DEF, closed)
          .isNull());
  ASSERT_TRUE(rr->rewriteViaRule(ProofRewriteRule::MACRO_QUANT_MACRO_DEF, open)
                  .isNull());

  // A function bound by the quantifier cannot become a free defined symbol.
  Node f = d_nodeManager->mkBoundVar("f", predType);
  Node fx = d_nodeManager->mkNode(Kind::APPLY_UF, f, x);
  Node bound = d_nodeManager->mkNode(
      Kind::FORALL, d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, f, x), fx);
  ASSERT_TRUE(rr->rewriteViaRule(ProofRewriteRule::MACRO_QUANT_MACRO_DEF, bound)
                  .isNull());

  // Nor may a compound operator depend on a variable bound by the formula.
  Node op = d_nodeManager->mkNode(Kind::LAMBDA, bvl, py);
  Node app = d_nodeManager->mkNode(Kind::APPLY_UF, op, y);
  Node dependent = d_nodeManager->mkNode(
      Kind::FORALL, d_nodeManager->mkNode(Kind::BOUND_VAR_LIST, y), app);
  ASSERT_TRUE(
      rr->rewriteViaRule(ProofRewriteRule::MACRO_QUANT_MACRO_DEF, dependent)
          .isNull());
}

}  // namespace test
}  // namespace cvc5::internal
