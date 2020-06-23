/*********************                                                        */
/*! \file node_builder_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::NodeBuilder.
 **
 ** Black box testing of CVC4::NodeBuilder.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <limits.h>
#include <sstream>

#include "base/check.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "test_utils.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class NodeBuilderBlack : public CxxTest::TestSuite {
private:

  NodeManager* d_nm;
  NodeManagerScope* d_scope;
  TypeNode* d_booleanType;
  TypeNode* d_integerType;
  TypeNode* d_realType;

 public:
  void setUp() override
  {
    d_nm = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nm);

    specKind = AND;
    d_integerType = new TypeNode(d_nm->integerType());
    d_booleanType = new TypeNode(d_nm->booleanType());
    d_realType = new TypeNode(d_nm->realType());
  }

  void tearDown() override
  {
    delete d_integerType;
    delete d_booleanType;
    delete d_realType;
    delete d_scope;
    delete d_nm;
  }


  template <unsigned N>
  void push_back(NodeBuilder<N>& nb, int n){
    for(int i = 0; i < n; ++i){
      nb << d_nm->mkConst(true);
    }
  }

#define K 30u
#define LARGE_K UINT_MAX / 40

  Kind specKind;

  /**
   * Tests just constructors. No modification is done to the node.
   */
  void testNodeConstructors() {

    //inline NodeBuilder();
    //inline NodeBuilder(Kind k);
    //inline NodeBuilder(const NodeBuilder<nchild_thresh>& nb);
    //template <unsigned N> inline NodeBuilder(const NodeBuilder<N>& nb);
    //inline NodeBuilder(NodeManager* nm);
    //inline NodeBuilder(NodeManager* nm, Kind k);

    /* default size tests */
    NodeBuilder<> def;
    TS_ASSERT_EQUALS(def.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(def.getNumChildren());
    TS_UTILS_EXPECT_ABORT(def.begin());
    TS_UTILS_EXPECT_ABORT(def.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> spec(specKind);
    TS_ASSERT_EQUALS(spec.getKind(), specKind);
    TS_ASSERT_EQUALS(spec.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(spec.begin(), spec.end());


    NodeBuilder<> from_nm(d_nm);
    TS_ASSERT_EQUALS(from_nm.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(from_nm.getNumChildren());
    TS_UTILS_EXPECT_ABORT(from_nm.begin());
    TS_UTILS_EXPECT_ABORT(from_nm.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> from_nm_kind(d_nm, specKind);
    TS_ASSERT_EQUALS(from_nm_kind.getKind(), specKind);
    TS_ASSERT_EQUALS(from_nm_kind.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(from_nm_kind.begin(), from_nm_kind.end());


    /* Non-default size tests */

    NodeBuilder<K> ws;
    TS_ASSERT_EQUALS(ws.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(ws.getNumChildren());
    TS_UTILS_EXPECT_ABORT(ws.begin());
    TS_UTILS_EXPECT_ABORT(ws.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<K> ws_kind(specKind);
    TS_ASSERT_EQUALS(ws_kind.getKind(), specKind);
    TS_ASSERT_EQUALS(ws_kind.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(ws_kind.begin(), ws_kind.end());


    NodeBuilder<K> ws_from_nm(d_nm);
    TS_ASSERT_EQUALS(ws_from_nm.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(ws_from_nm.getNumChildren());
    TS_UTILS_EXPECT_ABORT(ws_from_nm.begin());
    TS_UTILS_EXPECT_ABORT(ws_from_nm.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<K> ws_from_nm_kind(d_nm, specKind);
    TS_ASSERT_EQUALS(ws_from_nm_kind.getKind(), specKind);
    TS_ASSERT_EQUALS(ws_from_nm_kind.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(ws_from_nm_kind.begin(), ws_from_nm_kind.end());


    /* Extreme size tests */
    NodeBuilder<0> ws_size_0;

    // Allocating on the heap instead of the stack.
    NodeBuilder<LARGE_K>* ws_size_large =
      new NodeBuilder<LARGE_K>;
    delete ws_size_large;

    /* CopyConstructors */

    NodeBuilder<> copy(def);
    TS_ASSERT_EQUALS(copy.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(copy.getNumChildren());
    TS_UTILS_EXPECT_ABORT(copy.begin());
    TS_UTILS_EXPECT_ABORT(copy.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<K> cp_ws(ws);
    TS_ASSERT_EQUALS(cp_ws.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(cp_ws.getNumChildren());
    TS_UTILS_EXPECT_ABORT(cp_ws.begin());
    TS_UTILS_EXPECT_ABORT(cp_ws.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<K-10> cp_from_larger(ws);
    TS_ASSERT_EQUALS(cp_from_larger.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(cp_from_larger.getNumChildren());
    TS_UTILS_EXPECT_ABORT(cp_from_larger.begin());
    TS_UTILS_EXPECT_ABORT(cp_from_larger.end());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<K+10> cp_from_smaller(ws);
    TS_ASSERT_EQUALS(cp_from_smaller.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(cp_from_smaller.getNumChildren());
    TS_UTILS_EXPECT_ABORT(cp_from_smaller.begin());
    TS_UTILS_EXPECT_ABORT(cp_from_smaller.end());
#endif /* CVC4_ASSERTIONS */
  }

  void testDestructor() {
    //inline ~NodeBuilder();
    NodeBuilder<K>* nb = new NodeBuilder<K>();
    delete nb;
    //Not sure what to test other than survival
  }

  void testBeginEnd() {
    /* Test begin and ends without resizing */
    NodeBuilder<K> ws(specKind);
    TS_ASSERT_EQUALS(ws.begin(), ws.end());

    push_back(ws, K);
    TS_ASSERT_DIFFERS(ws.begin(), ws.end());

    NodeBuilder<K>::iterator iter = ws.begin();
    for(unsigned i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(iter, ws.end());
      ++iter;
    }
    TS_ASSERT_EQUALS(iter, ws.end());

    NodeBuilder<K>::const_iterator citer = ws.begin();
    for(unsigned i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(citer, ws.end());
      ++citer;
    }
    TS_ASSERT_EQUALS(citer, ws.end());

    /* Do the same tests and make sure that resizing occurs */

    NodeBuilder<> smaller(specKind);
    TS_ASSERT_EQUALS(smaller.begin(), smaller.end());

    push_back(smaller, K);
    TS_ASSERT_DIFFERS(smaller.begin(), smaller.end());

    NodeBuilder<>::iterator smaller_iter = smaller.begin();
    for(unsigned i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(smaller_iter, smaller.end());
      ++smaller_iter;
    }
    TS_ASSERT_EQUALS(iter, ws.end());

    NodeBuilder<>::const_iterator smaller_citer = smaller.begin();
    for(unsigned i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(smaller_citer, smaller.end());
      ++smaller_citer;
    }
    TS_ASSERT_EQUALS(smaller_citer, smaller.end());
  }

  void testIterator() {
    NodeBuilder<> b;
    Node x = d_nm->mkSkolem("x", *d_booleanType);
    Node y = d_nm->mkSkolem("z", *d_booleanType);
    Node z = d_nm->mkSkolem("y", *d_booleanType);
    b << x << y << z << AND;

    {
      NodeBuilder<>::iterator i = b.begin();
      TS_ASSERT(*i++ == x);
      TS_ASSERT(*i++ == y);
      TS_ASSERT(*i++ == z);
      TS_ASSERT(i == b.end());
    }

    {
      const NodeBuilder<>& c = b;
      NodeBuilder<>::const_iterator i = c.begin();
      TS_ASSERT(*i++ == x);
      TS_ASSERT(*i++ == y);
      TS_ASSERT(*i++ == z);
      TS_ASSERT(i == b.end());
    }
  }

  void testGetKind() {
    /*  Kind getKind() const; */
    NodeBuilder<> noKind;
    TS_ASSERT_EQUALS(noKind.getKind(), UNDEFINED_KIND);

    Node x( d_nm->mkSkolem( "x", *d_integerType ) );
    noKind << x << x;
    //     push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getKind(), UNDEFINED_KIND);

    noKind << PLUS;

    TS_ASSERT_EQUALS(noKind.getKind(), PLUS);

    Node n = noKind;

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(noKind.getKind());
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> spec(PLUS);
    TS_ASSERT_EQUALS(spec.getKind(), PLUS);
    spec << x << x ;
    TS_ASSERT_EQUALS(spec.getKind(), PLUS);
  }

  void testGetNumChildren() {
    /* unsigned getNumChildren() const; */
    Node x( d_nm->mkSkolem( "x", *d_integerType ) );

    NodeBuilder<> nb;
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb.getNumChildren());
#endif /* CVC4_ASSERTIONS */
    nb << PLUS << x << x;

    TS_ASSERT_EQUALS(nb.getNumChildren(), 2u);

    nb << x << x;
    TS_ASSERT_EQUALS(nb.getNumChildren(), 4u);

    Node n = nb;// avoid warning on clear()
    nb.clear();
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb.getNumChildren());
#endif /* CVC4_ASSERTIONS */
    nb.clear(PLUS);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0u);
    nb << x << x << x;

    TS_ASSERT_EQUALS(nb.getNumChildren(), 3u);

    nb << x << x << x;
    TS_ASSERT_EQUALS(nb.getNumChildren(), 6u);

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb << PLUS);
    n = nb;
    TS_UTILS_EXPECT_ABORT(nb.getNumChildren());
#endif /* CVC4_ASSERTIONS */
  }

  void testOperatorSquare() {
    /*
      Node operator[](int i) const {
      TS_ASSERT(i >= 0 && i < d_ev->getNumChildren());
      return Node(d_ev->d_children[i]);
      }
    */
    NodeBuilder<> arr(specKind);

    Node i_0 = d_nm->mkConst(false);
    Node i_2 = d_nm->mkConst(true);
    Node i_K = d_nm->mkNode(NOT, i_0);

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(arr[-1]);
    TS_UTILS_EXPECT_ABORT(arr[0]);
#endif /* CVC4_ASSERTIONS */

    arr << i_0;

    TS_ASSERT_EQUALS(arr[0], i_0);

    push_back(arr,1);

    arr << i_2;

    TS_ASSERT_EQUALS(arr[0], i_0);
    TS_ASSERT_EQUALS(arr[2], i_2);

    push_back(arr, K - 3);

    TS_ASSERT_EQUALS(arr[0], i_0);
    TS_ASSERT_EQUALS(arr[2], i_2);
    for(unsigned i = 3; i < K; ++i) {
      TS_ASSERT_EQUALS(arr[i], d_nm->mkConst(true));
    }

    arr << i_K;

    TS_ASSERT_EQUALS(arr[0], i_0);
    TS_ASSERT_EQUALS(arr[2], i_2);
    for(unsigned i = 3; i < K; ++i) {
      TS_ASSERT_EQUALS(arr[i], d_nm->mkConst(true));
    }
    TS_ASSERT_EQUALS(arr[K], i_K);

#ifdef CVC4_ASSERTIONS
    Node n = arr;
    TS_UTILS_EXPECT_ABORT(arr[0]);
#endif /* CVC4_ASSERTIONS */
  }

  void testClear() {
    /* void clear(Kind k = UNDEFINED_KIND); */
    NodeBuilder<> nb;

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb.getNumChildren());
    TS_UTILS_EXPECT_ABORT(nb.begin());
    TS_UTILS_EXPECT_ABORT(nb.end());
#endif /* CVC4_ASSERTIONS */

    nb << specKind;
    push_back(nb, K);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

    Node n = nb;// avoid warning on clear()
    nb.clear();

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb.getNumChildren());
    TS_UTILS_EXPECT_ABORT(nb.begin());
    TS_UTILS_EXPECT_ABORT(nb.end());
#endif /* CVC4_ASSERTIONS */

    nb << specKind;
    push_back(nb, K);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

    n = nb;// avoid warning on clear()
    nb.clear(specKind);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

    push_back(nb, K);
    n = nb;// avoid warning on clear()
    nb.clear();

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb.getNumChildren());
    TS_UTILS_EXPECT_ABORT(nb.begin());
    TS_UTILS_EXPECT_ABORT(nb.end());
#endif /* CVC4_ASSERTIONS */
  }

  void testStreamInsertionKind() {
    /* NodeBuilder& operator<<(const Kind& k); */

#ifdef CVC4_ASSERTIONS
    NodeBuilder<> spec(specKind);
    TS_UTILS_EXPECT_ABORT(spec << PLUS);
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> noSpec;
    noSpec << specKind;
    TS_ASSERT_EQUALS(noSpec.getKind(), specKind);


    NodeBuilder<> modified;
    push_back(modified, K);
    modified << specKind;
    TS_ASSERT_EQUALS(modified.getKind(), specKind);

    NodeBuilder<> nb(specKind);
    nb << d_nm->mkConst(true) << d_nm->mkConst(false);
    Node n = nb;// avoid warning on clear()
    nb.clear(PLUS);

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(n = nb);
    nb.clear(PLUS);
#endif /* CVC4_ASSERTIONS */

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(nb << PLUS);
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> testRef;
    TS_ASSERT_EQUALS((testRef << specKind).getKind(), specKind);

#ifdef CVC4_ASSERTIONS
    NodeBuilder<> testTwo;
    TS_UTILS_EXPECT_ABORT(testTwo << specKind << PLUS);
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> testMixOrder1;
    TS_ASSERT_EQUALS((testMixOrder1 << specKind << d_nm->mkConst(true)).getKind(),
                     specKind);
    NodeBuilder<> testMixOrder2;
    TS_ASSERT_EQUALS((testMixOrder2 << d_nm->mkConst(true) << specKind).getKind(),
                     specKind);
  }

  void testStreamInsertionNode() {
    /* NodeBuilder& operator<<(const Node& n); */
    NodeBuilder<K> nb(specKind);
    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());
    push_back(nb,K);
    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

#ifdef CVC4_ASSERTIONS
    Node n = nb;
    TS_UTILS_EXPECT_ABORT(nb << n);
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> overflow(specKind);
    TS_ASSERT_EQUALS(overflow.getKind(), specKind);
    TS_ASSERT_EQUALS(overflow.getNumChildren(), 0u);
    TS_ASSERT_EQUALS(overflow.begin(), overflow.end());

    push_back(overflow,5*K+1);

    TS_ASSERT_EQUALS(overflow.getKind(), specKind);
    TS_ASSERT_EQUALS(overflow.getNumChildren(), 5 * K + 1);
    TS_ASSERT_DIFFERS(overflow.begin(), overflow.end());

  }

  void testAppend() {
    Node x = d_nm->mkSkolem("x", *d_booleanType);
    Node y = d_nm->mkSkolem("y", *d_booleanType);
    Node z = d_nm->mkSkolem("z", *d_booleanType);
    Node m = d_nm->mkNode(AND, y, z, x);
    Node n = d_nm->mkNode(OR, d_nm->mkNode(NOT, x), y, z);
    Node o = d_nm->mkNode(XOR, y, x);

    Node r = d_nm->mkSkolem("r", *d_realType);
    Node s = d_nm->mkSkolem("s", *d_realType);
    Node t = d_nm->mkSkolem("t", *d_realType);

    Node p = d_nm->mkNode(EQUAL, d_nm->mkConst<Rational>(0),
                          d_nm->mkNode(PLUS, r, d_nm->mkNode(UMINUS, s), t));
    Node q = d_nm->mkNode(AND, x, z, d_nm->mkNode(NOT, y));

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(d_nm->mkNode(XOR, y, x, x));
#endif /* CVC4_ASSERTIONS */

    NodeBuilder<> b(specKind);

    // test append(TNode)
    b.append(n).append(o).append(q);

    TS_ASSERT(b.getNumChildren() == 3);
    TS_ASSERT(b[0] == n);
    TS_ASSERT(b[1] == o);
    TS_ASSERT(b[2] == q);

    vector<Node> v;
    v.push_back(m);
    v.push_back(p);
    v.push_back(q);
    // test append(vector<Node>)
    b.append(v);

    TS_ASSERT(b.getNumChildren() == 6);
    TS_ASSERT(b[0] == n);
    TS_ASSERT(b[1] == o);
    TS_ASSERT(b[2] == q);
    TS_ASSERT(b[3] == m);
    TS_ASSERT(b[4] == p);
    TS_ASSERT(b[5] == q);

    // test append(iterator, iterator)
    b.append(v.rbegin(), v.rend());

    TS_ASSERT(b.getNumChildren() == 9);
    TS_ASSERT(b[0] == n);
    TS_ASSERT(b[1] == o);
    TS_ASSERT(b[2] == q);
    TS_ASSERT(b[3] == m);
    TS_ASSERT(b[4] == p);
    TS_ASSERT(b[5] == q);
    TS_ASSERT(b[6] == q);
    TS_ASSERT(b[7] == p);
    TS_ASSERT(b[8] == m);
  }

  void testOperatorNodeCast() {
    /* operator Node();*/
    NodeBuilder<K> implicit(specKind);
    NodeBuilder<K> explic(specKind);

    push_back(implicit, K);
    push_back(explic, K);

    Node nimpl = implicit;
    Node nexplicit = (Node) explic;

    TS_ASSERT_EQUALS(nimpl.getKind(), specKind);
    TS_ASSERT_EQUALS(nimpl.getNumChildren(), K);

    TS_ASSERT_EQUALS(nexplicit.getKind(), specKind);
    TS_ASSERT_EQUALS(nexplicit.getNumChildren(), K);

#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(Node blah = implicit);
#endif /* CVC4_ASSERTIONS */
  }

  void testLeftistBuilding() {
    NodeBuilder<> nb;

    Node a = d_nm->mkSkolem("a", *d_booleanType);

    Node b = d_nm->mkSkolem("b", *d_booleanType);
    Node c = d_nm->mkSkolem("c", *d_booleanType);

    Node d = d_nm->mkSkolem("d", *d_realType);
    Node e = d_nm->mkSkolem("e", *d_realType);

    nb << a << NOT
       << b << c << OR
       << c << a << AND
       << d << e << ITE;

    Node n = nb;
    TS_ASSERT_EQUALS(n.getNumChildren(), 3u);
    TS_ASSERT_EQUALS(n.getType(), *d_realType);
    TS_ASSERT_EQUALS(n[0].getType(), *d_booleanType);
    TS_ASSERT_EQUALS(n[1].getType(), *d_realType);
    TS_ASSERT_EQUALS(n[2].getType(), *d_realType);

    Node nota = d_nm->mkNode(NOT, a);
    Node nota_or_b_or_c = d_nm->mkNode(OR, nota, b, c);
    Node n0 = d_nm->mkNode(AND, nota_or_b_or_c, c, a);
    Node nexpected = d_nm->mkNode(ITE, n0, d, e);

    TS_ASSERT_EQUALS(nexpected, n);
  }
};
