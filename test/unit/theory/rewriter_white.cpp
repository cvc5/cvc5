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

}  // namespace test
}  // namespace cvc5::internal
