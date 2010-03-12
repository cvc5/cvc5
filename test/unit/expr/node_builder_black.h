/*********************                                                        */
/** node__builder_black.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::NodeBuilder.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <limits.h>
#include <sstream>

#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "expr/kind.h"
#include "context/context.h"
#include "util/Assert.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class NodeBuilderBlack : public CxxTest::TestSuite {
private:

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);
    specKind = PLUS;
  }

  void tearDown() {
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }


  template <unsigned N>
  void push_back(NodeBuilder<N>& nb, int n){
    for(int i=0; i<n; ++i){
      nb << Node::null();
    }
  }

#define K 30
#define LARGE_K UINT_MAX/40

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
    TS_ASSERT_EQUALS(def.getNumChildren(), 0);
    TS_ASSERT_EQUALS(def.begin(), def.end());

    NodeBuilder<> spec(specKind);
    TS_ASSERT_EQUALS(spec.getKind(), specKind);
    TS_ASSERT_EQUALS(spec.getNumChildren(), 0);
    TS_ASSERT_EQUALS(spec.begin(), spec.end());


    NodeBuilder<> from_nm(d_nm);
    TS_ASSERT_EQUALS(from_nm.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(from_nm.getNumChildren(), 0);
    TS_ASSERT_EQUALS(from_nm.begin(), from_nm.end());

    NodeBuilder<> from_nm_kind(d_nm, specKind);
    TS_ASSERT_EQUALS(from_nm_kind.getKind(), specKind);
    TS_ASSERT_EQUALS(from_nm_kind.getNumChildren(), 0);
    TS_ASSERT_EQUALS(from_nm_kind.begin(), from_nm_kind.end());


    /* Non-default size tests */

    NodeBuilder<K> ws;
    TS_ASSERT_EQUALS(ws.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(ws.getNumChildren(), 0);
    TS_ASSERT_EQUALS(ws.begin(), ws.end());

    NodeBuilder<K> ws_kind(specKind);
    TS_ASSERT_EQUALS(ws_kind.getKind(), specKind);
    TS_ASSERT_EQUALS(ws_kind.getNumChildren(), 0);
    TS_ASSERT_EQUALS(ws_kind.begin(), ws_kind.end());


    NodeBuilder<K> ws_from_nm(d_nm);
    TS_ASSERT_EQUALS(ws_from_nm.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(ws_from_nm.getNumChildren(), 0);
    TS_ASSERT_EQUALS(ws_from_nm.begin(), ws_from_nm.end());

    NodeBuilder<K> ws_from_nm_kind(d_nm, specKind);
    TS_ASSERT_EQUALS(ws_from_nm_kind.getKind(), specKind);
    TS_ASSERT_EQUALS(ws_from_nm_kind.getNumChildren(), 0);
    TS_ASSERT_EQUALS(ws_from_nm_kind.begin(), ws_from_nm_kind.end());


    /* Extreme size tests */
    NodeBuilder<0> ws_size_0();

    NodeBuilder<LARGE_K> ws_size_large();

    /* CopyConstructors */

    NodeBuilder<> copy(def);
    TS_ASSERT_EQUALS(copy.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(copy.getNumChildren(), 0);
    TS_ASSERT_EQUALS(copy.begin(), copy.end());

    NodeBuilder<K> cp_ws(ws);
    TS_ASSERT_EQUALS(cp_ws.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(cp_ws.getNumChildren(), 0);
    TS_ASSERT_EQUALS(cp_ws.begin(), cp_ws.end());


    NodeBuilder<K-10> cp_from_larger(ws);
    TS_ASSERT_EQUALS(cp_from_larger.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(cp_from_larger.getNumChildren(), 0);
    TS_ASSERT_EQUALS(cp_from_larger.begin(), cp_from_larger.end());

    NodeBuilder<K+10> cp_from_smaller(ws);
    TS_ASSERT_EQUALS(cp_from_smaller.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(cp_from_smaller.getNumChildren(), 0);
    TS_ASSERT_EQUALS(cp_from_smaller.begin(), cp_from_smaller.end());

  }

  void testDestructor() {
    //inline ~NodeBuilder();
    NodeBuilder<K>* nb = new NodeBuilder<K>();
    delete nb;
    //Not sure what to test other than survival
  }

  void testBeginEnd() {
    /* Test begin and ends without resizing */
    NodeBuilder<K> ws;
    TS_ASSERT_EQUALS(ws.begin(), ws.end());

    push_back(ws, K);
    TS_ASSERT_DIFFERS(ws.begin(), ws.end());

    NodeBuilder<K>::iterator iter = ws.begin();
    for(int i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(iter, ws.end());
      ++iter;
    }
    TS_ASSERT_EQUALS(iter, ws.end());

    NodeBuilder<K>::const_iterator citer = ws.begin();
    for(int i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(citer, ws.end());
      ++citer;
    }
    TS_ASSERT_EQUALS(citer, ws.end());

    /* Do the same tests and make sure that resizing occurs */

    NodeBuilder<> smaller;
    TS_ASSERT_EQUALS(smaller.begin(), smaller.end());

    push_back(smaller, K);
    TS_ASSERT_DIFFERS(smaller.begin(), smaller.end());

    NodeBuilder<>::iterator smaller_iter = smaller.begin();
    for(int i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(smaller_iter, smaller.end());
      ++smaller_iter;
    }
    TS_ASSERT_EQUALS(iter, ws.end());

    NodeBuilder<>::const_iterator smaller_citer = smaller.begin();
    for(int i = 0; i < K; ++i){
      TS_ASSERT_DIFFERS(smaller_citer, smaller.end());
      ++smaller_citer;
    }
    TS_ASSERT_EQUALS(smaller_citer, smaller.end());
  }

  void testIterator() {
    NodeBuilder<> b;
    Node x = d_nm->mkVar();
    Node y = d_nm->mkVar();
    Node z = d_nm->mkVar();
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
    push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getKind(), UNDEFINED_KIND);

    noKind << specKind;
    TS_ASSERT_EQUALS(noKind.getKind(), specKind);

    Node n = noKind;

#ifdef CVC4_DEBUG
    TS_ASSERT_THROWS_ANYTHING(noKind.getKind(););
#endif

    NodeBuilder<> spec(specKind);
    TS_ASSERT_EQUALS(spec.getKind(), specKind);
    push_back(spec, K);
    TS_ASSERT_EQUALS(spec.getKind(), specKind);
  }

  void testGetNumChildren() {
    /* unsigned getNumChildren() const; */

    NodeBuilder<> noKind;
    TS_ASSERT_EQUALS(noKind.getNumChildren(), 0);
    push_back(noKind, K);

    TS_ASSERT_EQUALS(noKind.getNumChildren(), K);

    push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getNumChildren(), K+K);

    noKind << AND;// avoid exception on marking it used
    Node n = noKind;// avoid warning on clear()
    noKind.clear();
    TS_ASSERT_EQUALS(noKind.getNumChildren(), 0);
    push_back(noKind, K);

    TS_ASSERT_EQUALS(noKind.getNumChildren(), K);

    push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getNumChildren(), K+K);

#ifdef CVC4_DEBUG
    noKind << specKind;
    n = noKind;
    TS_ASSERT_THROWS_ANYTHING( noKind.getNumChildren() );
#endif
  }

  void testOperatorSquare() {
    /*
      Node operator[](int i) const {
      Assert(i >= 0 && i < d_ev->getNumChildren());
      return Node(d_ev->d_children[i]);
      }
    */
    NodeBuilder<> arr(specKind);

    Node i_0 = d_nm->mkNode(FALSE);
    Node i_2 = d_nm->mkNode(TRUE);
    Node i_K = d_nm->mkNode(NOT);


#ifdef CVC4_DEBUG
    TS_ASSERT_THROWS_ANYTHING(arr[-1];);
    TS_ASSERT_THROWS_ANYTHING(arr[0];);
#endif

    arr << i_0;

    TS_ASSERT_EQUALS(arr[0], i_0);

    push_back(arr,1);

    arr << i_2;

    TS_ASSERT_EQUALS(arr[0], i_0);
    TS_ASSERT_EQUALS(arr[2], i_2);

    push_back(arr, K-3);

    TS_ASSERT_EQUALS(arr[0], i_0);
    TS_ASSERT_EQUALS(arr[2], i_2);
    for(int i=3;i<K;++i) TS_ASSERT_EQUALS(arr[i], Node::null());

    arr << i_K;


    TS_ASSERT_EQUALS(arr[0], i_0);
    TS_ASSERT_EQUALS(arr[2], i_2);
    for(int i=3;i<K;++i) TS_ASSERT_EQUALS(arr[i], Node::null());
    TS_ASSERT_EQUALS(arr[K], i_K);

#ifdef CVC4_DEBUG
    Node n = arr;
    TS_ASSERT_THROWS_ANYTHING(arr[0];);
#endif
  }

  void testClear() {
    /* void clear(Kind k = UNDEFINED_KIND); */
    NodeBuilder<> nb;

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

    nb << specKind;
    push_back(nb, K);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

    Node n = nb;// avoid warning on clear()
    nb.clear();

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

    nb << specKind;
    push_back(nb, K);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

    n = nb;// avoid warning on clear()
    nb.clear(specKind);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

    push_back(nb, K);
    n = nb;// avoid warning on clear()
    nb.clear();

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

  }

  void testStreamInsertionKind() {
    /* NodeBuilder& operator<<(const Kind& k); */

#ifdef CVC4_DEBUG
    NodeBuilder<> spec(specKind);
    TS_ASSERT_THROWS_ANYTHING( spec << PLUS; );
#endif

    NodeBuilder<> noSpec;
    noSpec << specKind;
    TS_ASSERT_EQUALS(noSpec.getKind(), specKind);


    NodeBuilder<> modified;
    push_back(modified, K);
    modified << specKind;
    TS_ASSERT_EQUALS(modified.getKind(), specKind);

    NodeBuilder<> nb(specKind);
    Node n = nb;// avoid warning on clear()
    nb.clear(PLUS);

#ifdef CVC4_DEBUG
    TS_ASSERT_THROWS_ANYTHING( nb << PLUS; );
#endif

    NodeBuilder<> testRef;
    TS_ASSERT_EQUALS((testRef << specKind).getKind(), specKind);

#ifdef CVC4_DEBUG
    NodeBuilder<> testTwo;
    TS_ASSERT_THROWS_ANYTHING(testTwo << specKind << PLUS;);
#endif

    NodeBuilder<> testMixOrder1;
    TS_ASSERT_EQUALS((testMixOrder1<< specKind << d_nm->mkNode(TRUE)).getKind(),
                     specKind);
    NodeBuilder<> testMixOrder2;
    TS_ASSERT_EQUALS((testMixOrder2<< d_nm->mkNode(TRUE)<<specKind).getKind(),
                     specKind);
  }

  void testStreamInsertionNode() {
    /* NodeBuilder& operator<<(const Node& n); */
    NodeBuilder<K> nb(specKind);
    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());
    push_back(nb,K);
    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

#ifdef CVC4_DEBUG
    Node n = nb;
    TS_ASSERT_THROWS_ANYTHING(nb << n;);
#endif

    NodeBuilder<> overflow(specKind);
    TS_ASSERT_EQUALS(overflow.getKind(), specKind);
    TS_ASSERT_EQUALS(overflow.getNumChildren(), 0);
    TS_ASSERT_EQUALS(overflow.begin(), overflow.end());

    push_back(overflow,5*K+1);

    TS_ASSERT_EQUALS(overflow.getKind(), specKind);
    TS_ASSERT_EQUALS(overflow.getNumChildren(), 5*K+1);
    TS_ASSERT_DIFFERS(overflow.begin(), overflow.end());

  }

  void testAppend() {
    Node x = d_nm->mkVar();
    Node y = d_nm->mkVar();
    Node z = d_nm->mkVar();
    Node m = d_nm->mkNode(AND, y, z, x);
    Node n = d_nm->mkNode(OR, d_nm->mkNode(NOT, x), y, z);
    Node o = d_nm->mkNode(XOR, y, x, z);
    Node p = d_nm->mkNode(PLUS, z, d_nm->mkNode(UMINUS, x), z);
    Node q = d_nm->mkNode(AND, x, z, d_nm->mkNode(NOT, y));

    NodeBuilder<> b;

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

#ifdef CVC4_DEBUG
    TS_ASSERT_THROWS_ANYTHING(Node blah = implicit);
#endif
  }

  void testToStream() {
    /* inline void toStream(std::ostream& out) const {
       d_ev->toStream(out);
       }
     */

    NodeBuilder<K> a(specKind);
    NodeBuilder<K> b(specKind);
    NodeBuilder<K> c(TRUE);
    string astr, bstr, cstr;
    stringstream astream, bstream, cstream;

    push_back(a,K/2);
    push_back(b,K/2);
    push_back(c,K/2);

    a.toStream(astream);
    b.toStream(bstream);
    c.toStream(cstream);

    astr = astream.str();
    bstr = bstream.str();
    cstr = cstream.str();

    TS_ASSERT_EQUALS(astr, bstr);
    TS_ASSERT_DIFFERS(astr, cstr);

    Node n = a; n = b; n = c;// avoid warning on clear()
    a.clear(specKind);
    b.clear(specKind);
    c.clear(specKind);
    astream.flush();
    bstream.flush();
    cstream.flush();

    push_back(a,2*K);
    push_back(b,2*K);
    push_back(c,2*K+1);

    a.toStream(astream);
    b.toStream(bstream);
    c.toStream(cstream);

    astr = astream.str();
    bstr = bstream.str();
    cstr = cstream.str();

    TS_ASSERT_EQUALS(astr, bstr);
    TS_ASSERT_DIFFERS(astr, cstr);
  }

  void testConvenienceBuilders() {
    Node a = d_nm->mkVar();
    Node b = d_nm->mkVar();
    Node c = d_nm->mkVar();
    Node d = d_nm->mkVar();
    Node e = d_nm->mkVar();
    Node f = d_nm->mkVar();

    Node m = a && b;
    Node n = a && b || c;
    Node o = d + e - b;
    Node p = a && o || c;

    Node x = d + e + o - m;
    Node y = f - a - c + e;

    Node q = a && b && c;

    Node r = e && d && b && a || x && y || f || q && a;

    TS_ASSERT_EQUALS(m, d_nm->mkNode(AND, a, b));
    TS_ASSERT_EQUALS(n, d_nm->mkNode(OR, m, c));
    TS_ASSERT_EQUALS(o, d_nm->mkNode(PLUS, d, e, d_nm->mkNode(UMINUS, b)));
    TS_ASSERT_EQUALS(p, d_nm->mkNode(OR, d_nm->mkNode(AND, a, o), c));

    TS_ASSERT_EQUALS(x, d_nm->mkNode(PLUS, d, e, o, d_nm->mkNode(UMINUS, m)));
    TS_ASSERT_EQUALS(y, d_nm->mkNode(PLUS,
                                     f,
                                     d_nm->mkNode(UMINUS, a),
                                     d_nm->mkNode(UMINUS, c),
                                     e));

    TS_ASSERT_EQUALS(q, d_nm->mkNode(AND, a, b, c));

    TS_ASSERT_EQUALS(r, d_nm->mkNode(OR,
                                     d_nm->mkNode(AND, e, d, b, a),
                                     d_nm->mkNode(AND, x, y),
                                     f,
                                     d_nm->mkNode(AND, q, a)));

    TS_ASSERT_EQUALS(Node((a && b) && c), d_nm->mkNode(AND, a, b, c));
    TS_ASSERT_EQUALS(Node(a && (b && c)), d_nm->mkNode(AND, a, d_nm->mkNode(AND, b, c)));
    TS_ASSERT_EQUALS(Node((a || b) || c), d_nm->mkNode(OR, a, b, c));
    TS_ASSERT_EQUALS(Node(a || (b || c)), d_nm->mkNode(OR, a, d_nm->mkNode(OR, b, c)));
    TS_ASSERT_EQUALS(Node((a && b) || c), d_nm->mkNode(OR, d_nm->mkNode(AND, a, b), c));
    TS_ASSERT_EQUALS(Node(a && (b || c)), d_nm->mkNode(AND, a, d_nm->mkNode(OR, b, c)));
    TS_ASSERT_EQUALS(Node((a || b) && c), d_nm->mkNode(AND, d_nm->mkNode(OR, a, b), c));
    TS_ASSERT_EQUALS(Node(a || (b && c)), d_nm->mkNode(OR, a, d_nm->mkNode(AND, b, c)));

    TS_ASSERT_EQUALS(Node((a + b) + c), d_nm->mkNode(PLUS, a, b, c));
    TS_ASSERT_EQUALS(Node(a + (b + c)), d_nm->mkNode(PLUS, a, d_nm->mkNode(PLUS, b, c)));
    TS_ASSERT_EQUALS(Node((a - b) - c), d_nm->mkNode(PLUS, a, d_nm->mkNode(UMINUS, b), d_nm->mkNode(UMINUS, c)));
    TS_ASSERT_EQUALS(Node(a - (b - c)), d_nm->mkNode(PLUS, a, d_nm->mkNode(UMINUS, d_nm->mkNode(PLUS, b, d_nm->mkNode(UMINUS, c)))));
    TS_ASSERT_EQUALS(Node((a * b) * c), d_nm->mkNode(MULT, a, b, c));
    TS_ASSERT_EQUALS(Node(a * (b * c)), d_nm->mkNode(MULT, a, d_nm->mkNode(MULT, b, c)));
    TS_ASSERT_EQUALS(Node((a + b) - c), d_nm->mkNode(PLUS, a, b, d_nm->mkNode(UMINUS, c)));
    TS_ASSERT_EQUALS(Node(a + (b - c)), d_nm->mkNode(PLUS, a, d_nm->mkNode(PLUS, b, d_nm->mkNode(UMINUS, c))));
    TS_ASSERT_EQUALS(Node((a - b) + c), d_nm->mkNode(PLUS, a, d_nm->mkNode(UMINUS, b), c));
    TS_ASSERT_EQUALS(Node(a - (b + c)), d_nm->mkNode(PLUS, a, d_nm->mkNode(UMINUS, d_nm->mkNode(PLUS, b, c))));
    TS_ASSERT_EQUALS(Node((a + b) * c), d_nm->mkNode(MULT, d_nm->mkNode(PLUS, a, b), c));
    TS_ASSERT_EQUALS(Node(a + (b * c)), d_nm->mkNode(PLUS, a, d_nm->mkNode(MULT, b, c)));
    TS_ASSERT_EQUALS(Node((a - b) * c), d_nm->mkNode(MULT, d_nm->mkNode(PLUS, a, d_nm->mkNode(UMINUS, b)), c));
    TS_ASSERT_EQUALS(Node(a - (b * c)), d_nm->mkNode(PLUS, a, d_nm->mkNode(UMINUS, d_nm->mkNode(MULT, b, c))));
    TS_ASSERT_EQUALS(Node((a * b) + c), d_nm->mkNode(PLUS, d_nm->mkNode(MULT, a, b), c));
    TS_ASSERT_EQUALS(Node(a * (b + c)), d_nm->mkNode(MULT, a, d_nm->mkNode(PLUS, b, c)));
    TS_ASSERT_EQUALS(Node((a * b) - c), d_nm->mkNode(PLUS, d_nm->mkNode(MULT, a, b), d_nm->mkNode(UMINUS, c)));
    TS_ASSERT_EQUALS(Node(a * (b - c)), d_nm->mkNode(MULT, a, d_nm->mkNode(PLUS, b, d_nm->mkNode(UMINUS, c))));

    TS_ASSERT_EQUALS(Node(-a), d_nm->mkNode(UMINUS, a));
    TS_ASSERT_EQUALS(Node(- a - b), d_nm->mkNode(PLUS, d_nm->mkNode(UMINUS, a), d_nm->mkNode(UMINUS, b)));
    TS_ASSERT_EQUALS(Node(- a + b), d_nm->mkNode(PLUS, d_nm->mkNode(UMINUS, a), b));
    TS_ASSERT_EQUALS(Node(- a * b), d_nm->mkNode(MULT, d_nm->mkNode(UMINUS, a), b));
  }

  /**
   * This tests the "stack builder"
   */
  void testStackBuilder() {
    try {
      for(unsigned i = 0; i < 100; ++i) {
        size_t n = 1 + (rand() % 50);

        // make a builder "b" with a backing store for n children
        makeStackNodeBuilder(b, n);

        // build one-past-the-end
        for(size_t j = 0; j <= n; ++j) {
          b << Node::null();
        }
      }
    } catch(Exception e) {
      std::cout << e;
    }
  }
};
