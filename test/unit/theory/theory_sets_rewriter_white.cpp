/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of sets rewriter
 */

#include "expr/dtype.h"
#include "expr/emptyset.h"
#include "test_smt.h"
#include "theory/sets/theory_sets_rewriter.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {

using namespace theory;
using namespace kind;
using namespace theory::sets;

namespace test {

typedef expr::Attribute<Node, Node> attribute;

class TestTheoryWhiteSetsRewriter : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    d_rewriter.reset(new TheorySetsRewriter());
  }
  std::unique_ptr<TheorySetsRewriter> d_rewriter;
};

TEST_F(TestTheoryWhiteSetsRewriter, map)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node one = d_nodeManager->mkConstInt(Rational(1));
  TypeNode stringType = d_nodeManager->stringType();
  TypeNode integerType = d_nodeManager->integerType();
  Node emptysetInteger =
      d_nodeManager->mkConst(EmptySet(d_nodeManager->mkSetType(integerType)));
  Node emptysetString =
      d_nodeManager->mkConst(EmptySet(d_nodeManager->mkSetType(stringType)));
  Node x = d_nodeManager->mkBoundVar("x", stringType);
  Node bound = d_nodeManager->mkNode(kind::BOUND_VAR_LIST, x);
  Node lambda = d_nodeManager->mkNode(LAMBDA, bound, one);

  // (set.map (lambda ((x U))  t) (as set.empty (Set String)) =
  // (as set.empty (Set Int))
  Node n1 = d_nodeManager->mkNode(SET_MAP, lambda, emptysetString);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == emptysetInteger
              && response1.d_status == REWRITE_DONE);

  Node a = d_nodeManager->mkConst(String("a"));
  Node b = d_nodeManager->mkConst(String("b"));
  Node A = d_nodeManager->mkNode(SET_SINGLETON, a);
  Node B = d_nodeManager->mkNode(SET_SINGLETON, b);
  Node unionAB = d_nodeManager->mkNode(SET_UNION, A, B);

  // (set.map
  //   (lambda ((x String)) 1)
  //   (set.union (set.singleton "a") (set.singleton "b"))) = (set.singleton 1))
  Node n2 = d_nodeManager->mkNode(SET_MAP, lambda, unionAB);
  Node rewritten2 = rr->rewrite(n2);
  Node bag = d_nodeManager->mkNode(SET_SINGLETON, one);
  ASSERT_TRUE(rewritten2 == bag);

  //  - (set.map f (set.union K1 K2)) =
  //      (set.union (set.map f K1) (set.map f K2))
  Node k1 = d_skolemManager->mkDummySkolem("K1", A.getType());
  Node k2 = d_skolemManager->mkDummySkolem("K2", A.getType());
  Node f = d_skolemManager->mkDummySkolem("f", lambda.getType());
  Node unionK1K2 = d_nodeManager->mkNode(SET_UNION, k1, k2);
  Node n3 = d_nodeManager->mkNode(SET_MAP, f, unionK1K2);
  Node rewritten3 = rr->rewrite(n3);
  Node mapK1 = d_nodeManager->mkNode(SET_MAP, f, k1);
  Node mapK2 = d_nodeManager->mkNode(SET_MAP, f, k2);
  Node unionMapK1K2 = d_nodeManager->mkNode(SET_UNION, mapK1, mapK2);
  ASSERT_TRUE(rewritten3 == unionMapK1K2);
}

}  // namespace test
}  // namespace cvc5::internal
