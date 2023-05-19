/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::NodeBuilder.
 */

#include <limits.h>

#include <sstream>
#include <vector>

#include "base/check.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "test_node.h"
#include "util/rational.h"

#define K 30u
#define LARGE_K UINT_MAX / 40

namespace cvc5::internal {

using namespace kind;

namespace test {

class TestNodeBlackNodeBuilder : public TestNode
{
 protected:
  void push_back(NodeBuilder& nb, uint32_t n)
  {
    for (uint32_t i = 0; i < n; ++i)
    {
      nb << d_nodeManager->mkConst(true);
    }
  }
  Kind d_specKind = AND;
};

/** Tests just constructors. No modification is done to the node. */
TEST_F(TestNodeBlackNodeBuilder, ctors)
{
  /* Default size tests. */
  NodeBuilder def;
  ASSERT_EQ(def.getKind(), UNDEFINED_KIND);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(def.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder spec(d_specKind);
  ASSERT_EQ(spec.getKind(), d_specKind);
  ASSERT_EQ(spec.getNumChildren(), 0u);

  NodeBuilder from_nm(d_nodeManager);
  ASSERT_EQ(from_nm.getKind(), UNDEFINED_KIND);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(from_nm.getNumChildren(),
               "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder from_nm_kind(d_nodeManager, d_specKind);
  ASSERT_EQ(from_nm_kind.getKind(), d_specKind);
  ASSERT_EQ(from_nm_kind.getNumChildren(), 0u);

  /* Copy constructors */
  NodeBuilder copy(def);
  ASSERT_EQ(copy.getKind(), UNDEFINED_KIND);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(copy.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif
}

TEST_F(TestNodeBlackNodeBuilder, dtor)
{
  std::unique_ptr<NodeBuilder> nb(new NodeBuilder());
}

TEST_F(TestNodeBlackNodeBuilder, getKind)
{
  NodeBuilder noKind;
  ASSERT_EQ(noKind.getKind(), UNDEFINED_KIND);

  Node x(d_skolemManager->mkDummySkolem("x", *d_intTypeNode));
  noKind << x << x;
  ASSERT_EQ(noKind.getKind(), UNDEFINED_KIND);

  noKind << ADD;
  ASSERT_EQ(noKind.getKind(), ADD);

  Node n = noKind;
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(noKind.getKind(), "!isUsed\\(\\)");
#endif

  NodeBuilder spec(ADD);
  ASSERT_EQ(spec.getKind(), ADD);
  spec << x << x;
  ASSERT_EQ(spec.getKind(), ADD);
}

TEST_F(TestNodeBlackNodeBuilder, getNumChildren)
{
  Node x(d_skolemManager->mkDummySkolem("x", *d_intTypeNode));

  NodeBuilder nb;
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  nb << ADD << x << x;
  ASSERT_EQ(nb.getNumChildren(), 2u);

  nb << x << x;
  ASSERT_EQ(nb.getNumChildren(), 4u);

  nb.clear();
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  nb.clear(ADD);
  ASSERT_EQ(nb.getNumChildren(), 0u);

  nb << x << x << x;
  ASSERT_EQ(nb.getNumChildren(), 3u);

  nb << x << x << x;
  ASSERT_EQ(nb.getNumChildren(), 6u);

#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb << ADD, "getKind\\(\\) == kind::UNDEFINED_KIND");
  Node n = nb;
  ASSERT_DEATH(nb.getNumChildren(), "!isUsed\\(\\)");
#endif
}

TEST_F(TestNodeBlackNodeBuilder, operator_square)
{
  NodeBuilder arr(d_specKind);

  Node i_0 = d_nodeManager->mkConst(false);
  Node i_2 = d_nodeManager->mkConst(true);
  Node i_K = d_nodeManager->mkNode(NOT, i_0);

#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(arr[-1], "index out of range");
  ASSERT_DEATH(arr[0], "index out of range");
#endif

  arr << i_0;
  ASSERT_EQ(arr[0], i_0);

  push_back(arr, 1);
  arr << i_2;
  ASSERT_EQ(arr[0], i_0);
  ASSERT_EQ(arr[2], i_2);

  push_back(arr, K - 3);
  ASSERT_EQ(arr[0], i_0);
  ASSERT_EQ(arr[2], i_2);
  for (unsigned i = 3; i < K; ++i)
  {
    ASSERT_EQ(arr[i], d_nodeManager->mkConst(true));
  }

  arr << i_K;
  ASSERT_EQ(arr[0], i_0);
  ASSERT_EQ(arr[2], i_2);
  for (unsigned i = 3; i < K; ++i)
  {
    ASSERT_EQ(arr[i], d_nodeManager->mkConst(true));
  }
  ASSERT_EQ(arr[K], i_K);

#ifdef CVC5_ASSERTIONS
  Node n = arr;
  ASSERT_DEATH(arr[0], "!isUsed\\(\\)");
#endif
}

TEST_F(TestNodeBlackNodeBuilder, clear)
{
  NodeBuilder nb;
  ASSERT_EQ(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  nb << d_specKind;
  push_back(nb, K);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), K);

  nb.clear();
  ASSERT_EQ(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  nb << d_specKind;
  push_back(nb, K);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), K);

  nb.clear(d_specKind);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), 0u);

  push_back(nb, K);
  nb.clear();
  ASSERT_EQ(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif
}

TEST_F(TestNodeBlackNodeBuilder, operator_stream_insertion_kind)
{
#ifdef CVC5_ASSERTIONS
  NodeBuilder spec(d_specKind);
  ASSERT_DEATH(spec << ADD, "can't redefine the Kind of a NodeBuilder");
#endif

  NodeBuilder noSpec;
  noSpec << d_specKind;
  ASSERT_EQ(noSpec.getKind(), d_specKind);

  NodeBuilder modified;
  push_back(modified, K);
  modified << d_specKind;
  ASSERT_EQ(modified.getKind(), d_specKind);

  NodeBuilder nb(d_specKind);
  nb << d_nodeManager->mkConst(true) << d_nodeManager->mkConst(false);
  nb.clear(ADD);

#ifdef CVC5_ASSERTIONS
  Node n;
  ASSERT_DEATH(n = nb, "Nodes with kind `\\+` must have at least 2 children");
  nb.clear(ADD);
#endif

#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(nb << ADD, "can't redefine the Kind of a NodeBuilder");
#endif

  NodeBuilder testRef;
  ASSERT_EQ((testRef << d_specKind).getKind(), d_specKind);

#ifdef CVC5_ASSERTIONS
  NodeBuilder testTwo;
  ASSERT_DEATH(testTwo << d_specKind << ADD,
               "can't redefine the Kind of a NodeBuilder");
#endif

  NodeBuilder testMixOrder1;
  ASSERT_EQ(
      (testMixOrder1 << d_specKind << d_nodeManager->mkConst(true)).getKind(),
      d_specKind);
  NodeBuilder testMixOrder2;
  ASSERT_EQ(
      (testMixOrder2 << d_nodeManager->mkConst(true) << d_specKind).getKind(),
      d_specKind);
}

TEST_F(TestNodeBlackNodeBuilder, operator_stream_insertion_node)
{
  NodeBuilder nb(d_specKind);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), 0u);
  push_back(nb, K);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), K);

#ifdef CVC5_ASSERTIONS
  Node n = nb;
  ASSERT_DEATH(nb << n, "!isUsed\\(\\)");
#endif

  NodeBuilder overflow(d_specKind);
  ASSERT_EQ(overflow.getKind(), d_specKind);
  ASSERT_EQ(overflow.getNumChildren(), 0u);

  push_back(overflow, 5 * K + 1);
  ASSERT_EQ(overflow.getKind(), d_specKind);
  ASSERT_EQ(overflow.getNumChildren(), 5 * K + 1);
}

TEST_F(TestNodeBlackNodeBuilder, append)
{
  Node x = d_skolemManager->mkDummySkolem("x", *d_boolTypeNode);
  Node y = d_skolemManager->mkDummySkolem("y", *d_boolTypeNode);
  Node z = d_skolemManager->mkDummySkolem("z", *d_boolTypeNode);
  Node m = d_nodeManager->mkNode(AND, y, z, x);
  Node n = d_nodeManager->mkNode(OR, d_nodeManager->mkNode(NOT, x), y, z);
  Node o = d_nodeManager->mkNode(XOR, y, x);

  Node r = d_skolemManager->mkDummySkolem("r", *d_realTypeNode);
  Node s = d_skolemManager->mkDummySkolem("s", *d_realTypeNode);
  Node t = d_skolemManager->mkDummySkolem("t", *d_realTypeNode);

  Node p = d_nodeManager->mkNode(
      EQUAL,
      d_nodeManager->mkConst<Rational>(CONST_RATIONAL, 0),
      d_nodeManager->mkNode(ADD, r, d_nodeManager->mkNode(NEG, s), t));
  Node q = d_nodeManager->mkNode(AND, x, z, d_nodeManager->mkNode(NOT, y));

#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(d_nodeManager->mkNode(XOR, y, x, x),
               "Nodes with kind `xor` must have at most 2 children");
#endif

  NodeBuilder b(d_specKind);

  /* test append(TNode) */
  b.append(n).append(o).append(q);

  ASSERT_EQ(b.getNumChildren(), 3);
  ASSERT_EQ(b[0], n);
  ASSERT_EQ(b[1], o);
  ASSERT_EQ(b[2], q);

  std::vector<Node> v;
  v.push_back(m);
  v.push_back(p);
  v.push_back(q);

  /* test append(vector<Node>) */
  b.append(v);

  ASSERT_EQ(b.getNumChildren(), 6);
  ASSERT_EQ(b[0], n);
  ASSERT_EQ(b[1], o);
  ASSERT_EQ(b[2], q);
  ASSERT_EQ(b[3], m);
  ASSERT_EQ(b[4], p);
  ASSERT_EQ(b[5], q);

  /* test append(iterator, iterator) */
  b.append(v.rbegin(), v.rend());

  ASSERT_EQ(b.getNumChildren(), 9);
  ASSERT_EQ(b[0], n);
  ASSERT_EQ(b[1], o);
  ASSERT_EQ(b[2], q);
  ASSERT_EQ(b[3], m);
  ASSERT_EQ(b[4], p);
  ASSERT_EQ(b[5], q);
  ASSERT_EQ(b[6], q);
  ASSERT_EQ(b[7], p);
  ASSERT_EQ(b[8], m);
}

TEST_F(TestNodeBlackNodeBuilder, operator_node_cast)
{
  NodeBuilder implicit(d_specKind);
  NodeBuilder explic(d_specKind);

  push_back(implicit, K);
  push_back(explic, K);

  Node nimpl = implicit;
  Node nexplicit = (Node)explic;

  ASSERT_EQ(nimpl.getKind(), d_specKind);
  ASSERT_EQ(nimpl.getNumChildren(), K);

  ASSERT_EQ(nexplicit.getKind(), d_specKind);
  ASSERT_EQ(nexplicit.getNumChildren(), K);

#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(Node blah = implicit, "!isUsed\\(\\)");
#endif
}

TEST_F(TestNodeBlackNodeBuilder, leftist_building)
{
  NodeBuilder nb;

  Node a = d_skolemManager->mkDummySkolem("a", *d_boolTypeNode);

  Node b = d_skolemManager->mkDummySkolem("b", *d_boolTypeNode);
  Node c = d_skolemManager->mkDummySkolem("c", *d_boolTypeNode);

  Node d = d_skolemManager->mkDummySkolem("d", *d_realTypeNode);
  Node e = d_skolemManager->mkDummySkolem("e", *d_realTypeNode);

  nb << a << NOT << b << c << OR << c << a << AND << d << e << ITE;

  Node n = nb;
  ASSERT_EQ(n.getNumChildren(), 3u);
  ASSERT_EQ(n.getType(), *d_realTypeNode);
  ASSERT_EQ(n[0].getType(), *d_boolTypeNode);
  ASSERT_EQ(n[1].getType(), *d_realTypeNode);
  ASSERT_EQ(n[2].getType(), *d_realTypeNode);

  Node nota = d_nodeManager->mkNode(NOT, a);
  Node nota_or_b_or_c = d_nodeManager->mkNode(OR, nota, b, c);
  Node n0 = d_nodeManager->mkNode(AND, nota_or_b_or_c, c, a);
  Node nexpected = d_nodeManager->mkNode(ITE, n0, d, e);

  ASSERT_EQ(nexpected, n);
}
}  // namespace test
}  // namespace cvc5::internal
