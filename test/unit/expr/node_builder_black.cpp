/*********************                                                        */
/*! \file node_builder_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::NodeBuilder.
 **
 ** Black box testing of CVC4::NodeBuilder.
 **/

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

namespace CVC4 {

using namespace CVC4::kind;

namespace test {

class TestNodeBuilderBlackNode : public TestNodeBlack
{
 protected:
  template <unsigned N>
  void push_back(NodeBuilder<N>& nb, uint32_t n)
  {
    for (uint32_t i = 0; i < n; ++i)
    {
      nb << d_nodeManager->mkConst(true);
    }
  }
  Kind d_specKind = AND;
};

/** Tests just constructors. No modification is done to the node. */
TEST_F(TestNodeBuilderBlackNode, ctors)
{
  /* Default size tests. */
  NodeBuilder<> def;
  ASSERT_EQ(def.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(def.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(def.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(def.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<> spec(d_specKind);
  ASSERT_EQ(spec.getKind(), d_specKind);
  ASSERT_EQ(spec.getNumChildren(), 0u);
  ASSERT_EQ(spec.begin(), spec.end());

  NodeBuilder<> from_nm(d_nodeManager.get());
  ASSERT_EQ(from_nm.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(from_nm.getNumChildren(),
               "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(from_nm.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(from_nm.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<> from_nm_kind(d_nodeManager.get(), d_specKind);
  ASSERT_EQ(from_nm_kind.getKind(), d_specKind);
  ASSERT_EQ(from_nm_kind.getNumChildren(), 0u);
  ASSERT_EQ(from_nm_kind.begin(), from_nm_kind.end());

  /* Non-default size tests */
  NodeBuilder<K> ws;
  ASSERT_EQ(ws.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(ws.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(ws.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(ws.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<K> ws_kind(d_specKind);
  ASSERT_EQ(ws_kind.getKind(), d_specKind);
  ASSERT_EQ(ws_kind.getNumChildren(), 0u);
  ASSERT_EQ(ws_kind.begin(), ws_kind.end());

  NodeBuilder<K> ws_from_nm(d_nodeManager.get());
  ASSERT_EQ(ws_from_nm.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(ws_from_nm.getNumChildren(),
               "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(ws_from_nm.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(ws_from_nm.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<K> ws_from_nm_kind(d_nodeManager.get(), d_specKind);
  ASSERT_EQ(ws_from_nm_kind.getKind(), d_specKind);
  ASSERT_EQ(ws_from_nm_kind.getNumChildren(), 0u);
  ASSERT_EQ(ws_from_nm_kind.begin(), ws_from_nm_kind.end());

  /* Extreme size tests */
  NodeBuilder<0> ws_size_0;

  /* Allocating on the heap instead of the stack. */
  NodeBuilder<LARGE_K>* ws_size_large = new NodeBuilder<LARGE_K>;
  delete ws_size_large;

  /* Copy constructors */
  NodeBuilder<> copy(def);
  ASSERT_EQ(copy.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(copy.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(copy.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(copy.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<K> cp_ws(ws);
  ASSERT_EQ(cp_ws.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(cp_ws.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(cp_ws.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(cp_ws.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<K - 10> cp_from_larger(ws);
  ASSERT_EQ(cp_from_larger.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(cp_from_larger.getNumChildren(),
               "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(cp_from_larger.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(cp_from_larger.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  NodeBuilder<K + 10> cp_from_smaller(ws);
  ASSERT_EQ(cp_from_smaller.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(cp_from_smaller.getNumChildren(),
               "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(cp_from_smaller.begin(),
               "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(cp_from_smaller.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif
}

TEST_F(TestNodeBuilderBlackNode, dtor)
{
  NodeBuilder<K>* nb = new NodeBuilder<K>();
  delete nb;
}

TEST_F(TestNodeBuilderBlackNode, begin_end)
{
  /* Test begin() and end() without resizing. */
  NodeBuilder<K> ws(d_specKind);
  ASSERT_EQ(ws.begin(), ws.end());

  push_back(ws, K);
  ASSERT_NE(ws.begin(), ws.end());

  NodeBuilder<K>::iterator iter = ws.begin();
  for (uint32_t i = 0; i < K; ++i)
  {
    ASSERT_NE(iter, ws.end());
    ++iter;
  }
  ASSERT_EQ(iter, ws.end());

  NodeBuilder<K>::const_iterator citer = ws.begin();
  for (uint32_t i = 0; i < K; ++i)
  {
    ASSERT_NE(citer, ws.end());
    ++citer;
  }
  ASSERT_EQ(citer, ws.end());

  /* Repeat same tests and make sure that resizing occurs. */
  NodeBuilder<> smaller(d_specKind);
  ASSERT_EQ(smaller.begin(), smaller.end());

  push_back(smaller, K);
  ASSERT_NE(smaller.begin(), smaller.end());

  NodeBuilder<>::iterator smaller_iter = smaller.begin();
  for (uint32_t i = 0; i < K; ++i)
  {
    ASSERT_NE(smaller_iter, smaller.end());
    ++smaller_iter;
  }
  ASSERT_EQ(iter, ws.end());

  NodeBuilder<>::const_iterator smaller_citer = smaller.begin();
  for (uint32_t i = 0; i < K; ++i)
  {
    ASSERT_NE(smaller_citer, smaller.end());
    ++smaller_citer;
  }
  ASSERT_EQ(smaller_citer, smaller.end());
}

TEST_F(TestNodeBuilderBlackNode, iterator)
{
  NodeBuilder<> b;
  Node x = d_nodeManager->mkSkolem("x", *d_boolTypeNode);
  Node y = d_nodeManager->mkSkolem("z", *d_boolTypeNode);
  Node z = d_nodeManager->mkSkolem("y", *d_boolTypeNode);
  b << x << y << z << AND;

  {
    NodeBuilder<>::iterator i = b.begin();
    ASSERT_EQ(*i++, x);
    ASSERT_EQ(*i++, y);
    ASSERT_EQ(*i++, z);
    ASSERT_EQ(i, b.end());
  }

  {
    const NodeBuilder<>& c = b;
    NodeBuilder<>::const_iterator i = c.begin();
    ASSERT_EQ(*i++, x);
    ASSERT_EQ(*i++, y);
    ASSERT_EQ(*i++, z);
    ASSERT_EQ(i, b.end());
  }
}

TEST_F(TestNodeBuilderBlackNode, getKind)
{
  NodeBuilder<> noKind;
  ASSERT_EQ(noKind.getKind(), UNDEFINED_KIND);

  Node x(d_nodeManager->mkSkolem("x", *d_intTypeNode));
  noKind << x << x;
  ASSERT_EQ(noKind.getKind(), UNDEFINED_KIND);

  noKind << PLUS;

  ASSERT_EQ(noKind.getKind(), PLUS);

  Node n = noKind;

#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(noKind.getKind(), "!isUsed\\(\\)");
#endif

  NodeBuilder<> spec(PLUS);
  ASSERT_EQ(spec.getKind(), PLUS);
  spec << x << x;
  ASSERT_EQ(spec.getKind(), PLUS);
}

TEST_F(TestNodeBuilderBlackNode, getNumChildren)
{
  Node x(d_nodeManager->mkSkolem("x", *d_intTypeNode));

  NodeBuilder<> nb;
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif
  nb << PLUS << x << x;

  ASSERT_EQ(nb.getNumChildren(), 2u);

  nb << x << x;
  ASSERT_EQ(nb.getNumChildren(), 4u);

  nb.clear();
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif
  nb.clear(PLUS);
  ASSERT_EQ(nb.getNumChildren(), 0u);
  nb << x << x << x;

  ASSERT_EQ(nb.getNumChildren(), 3u);

  nb << x << x << x;
  ASSERT_EQ(nb.getNumChildren(), 6u);

#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb << PLUS, "getKind\\(\\) == kind::UNDEFINED_KIND");
  Node n = nb;
  ASSERT_DEATH(nb.getNumChildren(), "!isUsed\\(\\)");
#endif
}

TEST_F(TestNodeBuilderBlackNode, operator_square)
{
  NodeBuilder<> arr(d_specKind);

  Node i_0 = d_nodeManager->mkConst(false);
  Node i_2 = d_nodeManager->mkConst(true);
  Node i_K = d_nodeManager->mkNode(NOT, i_0);

#ifdef CVC4_ASSERTIONS
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

#ifdef CVC4_ASSERTIONS
  Node n = arr;
  ASSERT_DEATH(arr[0], "!isUsed\\(\\)");
#endif
}

TEST_F(TestNodeBuilderBlackNode, clear)
{
  NodeBuilder<> nb;

  ASSERT_EQ(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(nb.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(nb.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  nb << d_specKind;
  push_back(nb, K);

  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), K);
  ASSERT_NE(nb.begin(), nb.end());

  nb.clear();

  ASSERT_EQ(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(nb.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(nb.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif

  nb << d_specKind;
  push_back(nb, K);

  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), K);
  ASSERT_NE(nb.begin(), nb.end());

  nb.clear(d_specKind);

  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), 0u);
  ASSERT_EQ(nb.begin(), nb.end());

  push_back(nb, K);
  nb.clear();

  ASSERT_EQ(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb.getNumChildren(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(nb.begin(), "getKind\\(\\) != kind::UNDEFINED_KIND");
  ASSERT_DEATH(nb.end(), "getKind\\(\\) != kind::UNDEFINED_KIND");
#endif
}

TEST_F(TestNodeBuilderBlackNode, operator_stream_insertion_kind)
{
#ifdef CVC4_ASSERTIONS
  NodeBuilder<> spec(d_specKind);
  ASSERT_DEATH(spec << PLUS, "can't redefine the Kind of a NodeBuilder");
#endif

  NodeBuilder<> noSpec;
  noSpec << d_specKind;
  ASSERT_EQ(noSpec.getKind(), d_specKind);

  NodeBuilder<> modified;
  push_back(modified, K);
  modified << d_specKind;
  ASSERT_EQ(modified.getKind(), d_specKind);

  NodeBuilder<> nb(d_specKind);
  nb << d_nodeManager->mkConst(true) << d_nodeManager->mkConst(false);
  nb.clear(PLUS);

#ifdef CVC4_ASSERTIONS
  Node n;
  ASSERT_DEATH(n = nb, "Nodes with kind PLUS must have at least 2 children");
  nb.clear(PLUS);
#endif

#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(nb << PLUS, "can't redefine the Kind of a NodeBuilder");
#endif

  NodeBuilder<> testRef;
  ASSERT_EQ((testRef << d_specKind).getKind(), d_specKind);

#ifdef CVC4_ASSERTIONS
  NodeBuilder<> testTwo;
  ASSERT_DEATH(testTwo << d_specKind << PLUS,
               "can't redefine the Kind of a NodeBuilder");
#endif

  NodeBuilder<> testMixOrder1;
  ASSERT_EQ(
      (testMixOrder1 << d_specKind << d_nodeManager->mkConst(true)).getKind(),
      d_specKind);
  NodeBuilder<> testMixOrder2;
  ASSERT_EQ(
      (testMixOrder2 << d_nodeManager->mkConst(true) << d_specKind).getKind(),
      d_specKind);
}

TEST_F(TestNodeBuilderBlackNode, operator_stream_insertion_node)
{
  NodeBuilder<K> nb(d_specKind);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), 0u);
  ASSERT_EQ(nb.begin(), nb.end());
  push_back(nb, K);
  ASSERT_EQ(nb.getKind(), d_specKind);
  ASSERT_EQ(nb.getNumChildren(), K);
  ASSERT_NE(nb.begin(), nb.end());

#ifdef CVC4_ASSERTIONS
  Node n = nb;
  ASSERT_DEATH(nb << n, "!isUsed\\(\\)");
#endif

  NodeBuilder<> overflow(d_specKind);
  ASSERT_EQ(overflow.getKind(), d_specKind);
  ASSERT_EQ(overflow.getNumChildren(), 0u);
  ASSERT_EQ(overflow.begin(), overflow.end());

  push_back(overflow, 5 * K + 1);

  ASSERT_EQ(overflow.getKind(), d_specKind);
  ASSERT_EQ(overflow.getNumChildren(), 5 * K + 1);
  ASSERT_NE(overflow.begin(), overflow.end());
}

TEST_F(TestNodeBuilderBlackNode, append)
{
  Node x = d_nodeManager->mkSkolem("x", *d_boolTypeNode);
  Node y = d_nodeManager->mkSkolem("y", *d_boolTypeNode);
  Node z = d_nodeManager->mkSkolem("z", *d_boolTypeNode);
  Node m = d_nodeManager->mkNode(AND, y, z, x);
  Node n = d_nodeManager->mkNode(OR, d_nodeManager->mkNode(NOT, x), y, z);
  Node o = d_nodeManager->mkNode(XOR, y, x);

  Node r = d_nodeManager->mkSkolem("r", *d_realTypeNode);
  Node s = d_nodeManager->mkSkolem("s", *d_realTypeNode);
  Node t = d_nodeManager->mkSkolem("t", *d_realTypeNode);

  Node p = d_nodeManager->mkNode(
      EQUAL,
      d_nodeManager->mkConst<Rational>(0),
      d_nodeManager->mkNode(PLUS, r, d_nodeManager->mkNode(UMINUS, s), t));
  Node q = d_nodeManager->mkNode(AND, x, z, d_nodeManager->mkNode(NOT, y));

#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(d_nodeManager->mkNode(XOR, y, x, x),
               "Nodes with kind XOR must have at most 2 children");
#endif

  NodeBuilder<> b(d_specKind);

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

TEST_F(TestNodeBuilderBlackNode, operator_node_cast)
{
  NodeBuilder<K> implicit(d_specKind);
  NodeBuilder<K> explic(d_specKind);

  push_back(implicit, K);
  push_back(explic, K);

  Node nimpl = implicit;
  Node nexplicit = (Node)explic;

  ASSERT_EQ(nimpl.getKind(), d_specKind);
  ASSERT_EQ(nimpl.getNumChildren(), K);

  ASSERT_EQ(nexplicit.getKind(), d_specKind);
  ASSERT_EQ(nexplicit.getNumChildren(), K);

#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(Node blah = implicit, "!isUsed\\(\\)");
#endif
}

TEST_F(TestNodeBuilderBlackNode, leftist_building)
{
  NodeBuilder<> nb;

  Node a = d_nodeManager->mkSkolem("a", *d_boolTypeNode);

  Node b = d_nodeManager->mkSkolem("b", *d_boolTypeNode);
  Node c = d_nodeManager->mkSkolem("c", *d_boolTypeNode);

  Node d = d_nodeManager->mkSkolem("d", *d_realTypeNode);
  Node e = d_nodeManager->mkSkolem("e", *d_realTypeNode);

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
}  // namespace CVC4
