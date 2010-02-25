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

//Used in some of the tests
#include <vector>
#include <limits.h>
#include <sstream>

#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "expr/kind.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class NodeBuilderBlack : public CxxTest::TestSuite {
private:

  NodeManagerScope *d_scope;
  NodeManager *d_nm;

public:

  void setUp() {
    d_nm = new NodeManager();
    d_scope = new NodeManagerScope(d_nm);
    specKind = PLUS;
  }

  void tearDown() {
    delete d_nm;
    delete d_scope;
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
  void testNodeConstructors(){

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

  void testDestructor(){
    //inline ~NodeBuilder();
    NodeBuilder<K>* nb = new NodeBuilder<K>();
    delete nb;
    //Not sure what to test other than survival
  }

  void testBeginEnd(){
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

  void testIterator(){
    TS_WARN( "TODO: This test still needs to be written!" );
  }

  void testGetKind(){
    /*  Kind getKind() const; */
    NodeBuilder<> noKind;
    TS_ASSERT_EQUALS(noKind.getKind(), UNDEFINED_KIND);
    push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getKind(), UNDEFINED_KIND);

    noKind << specKind;
    TS_ASSERT_EQUALS(noKind.getKind(), specKind);

    Node n = noKind;

    TS_ASSERT_THROWS_ANYTHING(noKind.getKind(););



    NodeBuilder<> spec(specKind);
    TS_ASSERT_EQUALS(spec.getKind(), specKind);
    push_back(spec, K);
    TS_ASSERT_EQUALS(spec.getKind(), specKind);

  }

  void testGetNumChildren(){
    /* unsigned getNumChildren() const; */

    NodeBuilder<> noKind;
    TS_ASSERT_EQUALS(noKind.getNumChildren(), 0);
    push_back(noKind, K);

    TS_ASSERT_EQUALS(noKind.getNumChildren(), K);

    push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getNumChildren(), K+K);

    noKind.clear();
    TS_ASSERT_EQUALS(noKind.getNumChildren(), 0);
    push_back(noKind, K);

    TS_ASSERT_EQUALS(noKind.getNumChildren(), K);

    push_back(noKind, K);
    TS_ASSERT_EQUALS(noKind.getNumChildren(), K+K);


    noKind << specKind;
    Node n = noKind;
    TS_ASSERT_THROWS_ANYTHING(noKind.getNumChildren(););
  }

  void testOperatorSquare(){
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


    TS_ASSERT_THROWS_ANYTHING(arr[-1];);
    TS_ASSERT_THROWS_ANYTHING(arr[0];);


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

    Node n = arr;
    TS_ASSERT_THROWS_ANYTHING(arr[0];);
  }

  void testClear(){
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

    nb.clear();

    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

    nb << specKind;
    push_back(nb, K);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

    nb.clear(specKind);

    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

    push_back(nb, K);
    Node n = nb;
    nb.clear();


    TS_ASSERT_EQUALS(nb.getKind(), UNDEFINED_KIND);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());

  }

  void testStreamInsertionKind(){
    /* NodeBuilder& operator<<(const Kind& k); */

    NodeBuilder<> spec(specKind);
    TS_ASSERT_THROWS_ANYTHING( spec << PLUS; );

    NodeBuilder<> noSpec;
    noSpec << specKind;
    TS_ASSERT_EQUALS(noSpec.getKind(), specKind);


    NodeBuilder<> modified;
    push_back(modified, K);
    modified << specKind;
    TS_ASSERT_EQUALS(modified.getKind(), specKind);

    NodeBuilder<> nb(specKind);
    Node n = nb;
    nb.clear(PLUS);
    TS_ASSERT_THROWS_ANYTHING(nb << PLUS;);

    NodeBuilder<> testRef;
    TS_ASSERT_EQUALS((testRef << specKind).getKind(), specKind);


    NodeBuilder<> testTwo;
    TS_ASSERT_THROWS_ANYTHING(testTwo << specKind << PLUS;);

    NodeBuilder<> testMixOrder1;
    TS_ASSERT_EQUALS((testMixOrder1<< specKind << d_nm->mkNode(TRUE)).getKind(),
                     specKind);
    NodeBuilder<> testMixOrder2;
    TS_ASSERT_EQUALS((testMixOrder2<< d_nm->mkNode(TRUE)<<specKind).getKind(),
                     specKind);
  }

  void testStreamInsertionNode(){
    /* NodeBuilder& operator<<(const Node& n); */
    NodeBuilder<K> nb(specKind);
    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), 0);
    TS_ASSERT_EQUALS(nb.begin(), nb.end());
    push_back(nb,K);
    TS_ASSERT_EQUALS(nb.getKind(), specKind);
    TS_ASSERT_EQUALS(nb.getNumChildren(), K);
    TS_ASSERT_DIFFERS(nb.begin(), nb.end());

    Node n = nb;
    TS_ASSERT_THROWS_ANYTHING(nb << n;);


    NodeBuilder<> overflow(specKind);
    TS_ASSERT_EQUALS(overflow.getKind(), specKind);
    TS_ASSERT_EQUALS(overflow.getNumChildren(), 0);
    TS_ASSERT_EQUALS(overflow.begin(), overflow.end());

    push_back(overflow,5*K+1);

    TS_ASSERT_EQUALS(overflow.getKind(), specKind);
    TS_ASSERT_EQUALS(overflow.getNumChildren(), 5*K+1);
    TS_ASSERT_DIFFERS(overflow.begin(), overflow.end());

  }

  void testAppend(){
    /*
      NodeBuilder& append(const Node& n) {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    Debug("prop") << "append: " << this << " " << n << "[" << n.d_ev << "]" << std::endl;
    allocateEvIfNecessaryForAppend();
    NodeValue* ev = n.d_ev;
    ev->inc();
    d_ev->d_children[d_ev->d_nchildren++] = ev;
    return *this;
  }
     */
    /*
      
  template <class Iterator>
  NodeBuilder& append(const Iterator& begin, const Iterator& end) {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return *this;
  }

    */
    TS_WARN( "TODO: This test still needs to be written!" );
  }

  void testOperatorNodeCast(){
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

    TS_ASSERT_THROWS_ANYTHING(Node blah = implicit);
  }

  void testToStream(){
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
};
