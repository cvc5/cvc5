/*********************                                                        */
/** node_black.h
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): dejan, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

//Used in some of the tests
#include <vector>
#include <sstream>

#include "expr/expr_manager.h"
#include "expr/node_value.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class NodeBlack : public CxxTest::TestSuite {
private:

  Context* d_ctxt;
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;
  Type* d_booleanType;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nodeManager = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nodeManager);

    d_booleanType = d_nodeManager->booleanType();
  }

  void tearDown() {
    delete d_scope;
    delete d_nodeManager;
    delete d_ctxt;
  }

  bool imp(bool a, bool b) const {
    return (!a) || (b);
  }
  bool iff(bool a, bool b) const {
    return (a && b) || ((!a)&&(!b));
  }

  void testNull() {
    Node::null();
  }

  void testIsNull() {
    /* bool isNull() const; */

    Node a = Node::null();
    TS_ASSERT(a.isNull());

    Node b = Node();
    TS_ASSERT(b.isNull());

    Node c = b;

    TS_ASSERT(c.isNull());
  }

  void testCopyCtor() {
    Node e(Node::null());
  }

  void testDestructor() {
    /* No access to internals ?
     * Makes sense to only test that this is crash free.
     */

    Node *n = new Node();
    delete n;

  }

  /*tests:  bool operator==(const Node& e) const  */
  void testOperatorEquals() {
    Node a, b, c;

    b = d_nodeManager->mkVar(d_booleanType);

    a = b;
    c = a;

    Node d = d_nodeManager->mkVar(d_booleanType);

    TS_ASSERT(a==a);
    TS_ASSERT(a==b);
    TS_ASSERT(a==c);

    TS_ASSERT(b==a);
    TS_ASSERT(b==b);
    TS_ASSERT(b==c);



    TS_ASSERT(c==a);
    TS_ASSERT(c==b);
    TS_ASSERT(c==c);


    TS_ASSERT(d==d);

    TS_ASSERT(!(d==a));
    TS_ASSERT(!(d==b));
    TS_ASSERT(!(d==c));

    TS_ASSERT(!(a==d));
    TS_ASSERT(!(b==d));
    TS_ASSERT(!(c==d));

  }

  /* operator!= */
  void testOperatorNotEquals() {


    Node a, b, c;

    b = d_nodeManager->mkVar(d_booleanType);

    a = b;
    c = a;

    Node d = d_nodeManager->mkVar(d_booleanType);

    /*structed assuming operator == works */
    TS_ASSERT(iff(a!=a, !(a==a)));
    TS_ASSERT(iff(a!=b, !(a==b)));
    TS_ASSERT(iff(a!=c, !(a==c)));


    TS_ASSERT(iff(b!=a, !(b==a)));
    TS_ASSERT(iff(b!=b, !(b==b)));
    TS_ASSERT(iff(b!=c, !(b==c)));


    TS_ASSERT(iff(c!=a, !(c==a)));
    TS_ASSERT(iff(c!=b, !(c==b)));
    TS_ASSERT(iff(c!=c, !(c==c)));

    TS_ASSERT(!(d!=d));

    TS_ASSERT(d!=a);
    TS_ASSERT(d!=b);
    TS_ASSERT(d!=c);

  }

  void testOperatorSquare() {
    /*Node operator[](int i) const */

#ifdef CVC4_ASSERTIONS
    //Basic bounds check on a node w/out children
    TS_ASSERT_THROWS(Node::null()[-1], AssertionException);
    TS_ASSERT_THROWS(Node::null()[0], AssertionException);
#endif /* CVC4_ASSERTIONS */

    //Basic access check
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node ite = cnd.iteNode(tb, eb);

    TS_ASSERT(tb == cnd[0]);
    TS_ASSERT(eb == cnd[1]);

    TS_ASSERT(cnd == ite[0]);
    TS_ASSERT(tb == ite[1]);
    TS_ASSERT(eb == ite[2]);

#ifdef CVC4_ASSERTIONS
    //Bounds check on a node with children
    TS_ASSERT_THROWS(ite == ite[-1], AssertionException);
    TS_ASSERT_THROWS(ite == ite[4], AssertionException);
#endif /* CVC4_ASSERTIONS */
  }

  /*tests:   Node& operator=(const Node&); */
  void testOperatorAssign() {
    Node a, b;
    Node c = d_nodeManager->mkNode(NOT, d_nodeManager->mkVar(d_booleanType));

    b = c;
    TS_ASSERT(b==c);


    a = b = c;

    TS_ASSERT(a==b);
    TS_ASSERT(a==c);
  }

  void testOperatorLessThan() {
    /* We don't have access to the ids so we can't test the implementation
     * in the black box tests. */

    Node a = d_nodeManager->mkVar(d_nodeManager->booleanType(), "a");
    Node b = d_nodeManager->mkVar(d_nodeManager->booleanType(), "b");

    TS_ASSERT(a<b || b<a);
    TS_ASSERT(!(a<b && b<a));

    Node c = d_nodeManager->mkNode(AND, a, b);
    Node d = d_nodeManager->mkNode(AND, a, b);

    TS_ASSERT(!(c<d));
    TS_ASSERT(!(d<c));

    /* TODO:
     * Less than has the rather difficult to test property that subexpressions
     * are less than enclosing expressions.
     *
     * But what would be a convincing test of this property?
     */

    // simple test of descending descendant property
    Node child = d_nodeManager->mkConst(true);
    Node parent = d_nodeManager->mkNode(NOT, child);

    TS_ASSERT(child < parent);

    // slightly less simple test of DD property
    std::vector<Node> chain;
    const int N = 500;
    Node curr = d_nodeManager->mkNode(OR, a, b);
    chain.push_back(curr);
    for(int i = 0; i < N; ++i) {
      curr = d_nodeManager->mkNode(AND, curr, curr);
      chain.push_back(curr);
    }

    for(int i = 0; i < N; ++i) {
      for(int j = i + 1; j < N; ++j) {
	Node chain_i = chain[i];
	Node chain_j = chain[j];
	TS_ASSERT(chain_i < chain_j);
      }
    }
  }

  void testEqNode() {
    /* Node eqNode(const Node& right) const; */

    Node left = d_nodeManager->mkConst(true);
    Node right = d_nodeManager->mkNode(NOT, d_nodeManager->mkConst(false));
    Node eq = left.eqNode(right);

    TS_ASSERT(EQUAL == eq.getKind());
    TS_ASSERT(2 == eq.getNumChildren());

    TS_ASSERT(eq[0] == left);
    TS_ASSERT(eq[1] == right);
  }

  void testNotNode() {
    /* Node notNode() const; */

    Node child = d_nodeManager->mkConst(true);
    Node parent = child.notNode();

    TS_ASSERT(NOT == parent.getKind());
    TS_ASSERT(1   == parent.getNumChildren());

    TS_ASSERT(parent[0] == child);

  }
  void testAndNode() {
    /*Node andNode(const Node& right) const;*/

    Node left = d_nodeManager->mkConst(true);
    Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
    Node eq = left.andNode(right);


    TS_ASSERT(AND == eq.getKind());
    TS_ASSERT(2   == eq.getNumChildren());

    TS_ASSERT(*(eq.begin()) == left);
    TS_ASSERT(*(++eq.begin()) == right);

  }

  void testOrNode() {
    /*Node orNode(const Node& right) const;*/

    Node left = d_nodeManager->mkConst(true);
    Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
    Node eq = left.orNode(right);


    TS_ASSERT(OR  == eq.getKind());
    TS_ASSERT(2   == eq.getNumChildren());

    TS_ASSERT(*(eq.begin()) == left);
    TS_ASSERT(*(++eq.begin()) == right);

  }

  void testIteNode() {
    /*Node iteNode(const Node& thenpart, const Node& elsepart) const;*/

    Node a = d_nodeManager->mkVar(d_booleanType);
    Node b = d_nodeManager->mkVar(d_booleanType);

    Node cnd = d_nodeManager->mkNode(PLUS, a, b);
    Node thenBranch = d_nodeManager->mkConst(true);
    Node elseBranch = d_nodeManager->mkNode(NOT, d_nodeManager->mkConst(false));
    Node ite = cnd.iteNode(thenBranch, elseBranch);

    TS_ASSERT(ITE == ite.getKind());
    TS_ASSERT(3 == ite.getNumChildren());

    TS_ASSERT(*(ite.begin()) == cnd);
    TS_ASSERT(*(++ite.begin()) == thenBranch);
    TS_ASSERT(*(++(++ite.begin())) == elseBranch);
  }

  void testIffNode() {
    /*  Node iffNode(const Node& right) const; */

    Node left = d_nodeManager->mkConst(true);
    Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
    Node eq = left.iffNode(right);


    TS_ASSERT(IFF == eq.getKind());
    TS_ASSERT(2   == eq.getNumChildren());

    TS_ASSERT(*(eq.begin()) == left);
    TS_ASSERT(*(++eq.begin()) == right);
  }


  void testImpNode() {
    /* Node impNode(const Node& right) const; */
    Node left = d_nodeManager->mkConst(true);
    Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
    Node eq = left.impNode(right);


    TS_ASSERT(IMPLIES == eq.getKind());
    TS_ASSERT(2 == eq.getNumChildren());

    TS_ASSERT(*(eq.begin()) == left);
    TS_ASSERT(*(++eq.begin()) == right);
  }

  void testXorNode() {
    /*Node xorNode(const Node& right) const;*/
    Node left = d_nodeManager->mkConst(true);
    Node right = d_nodeManager->mkNode(NOT, (d_nodeManager->mkConst(false)));
    Node eq = left.xorNode(right);


    TS_ASSERT(XOR == eq.getKind());
    TS_ASSERT(2   == eq.getNumChildren());

    TS_ASSERT(*(eq.begin()) == left);
    TS_ASSERT(*(++eq.begin()) == right);
  }

  void testGetKind() {
    /*inline Kind getKind() const; */

    Node a = d_nodeManager->mkVar(d_booleanType);
    Node b = d_nodeManager->mkVar(d_booleanType);

    Node n = d_nodeManager->mkNode(NOT, a);
    TS_ASSERT(NOT == n.getKind());

    n = d_nodeManager->mkNode(IFF, a, b);
    TS_ASSERT(IFF == n.getKind());

    n = d_nodeManager->mkNode(PLUS, a, b);
    TS_ASSERT(PLUS == n.getKind());

    n = d_nodeManager->mkNode(UMINUS, a);
    TS_ASSERT(UMINUS == n.getKind());
  }

  void testGetOperator() {
    Type* sort = d_nodeManager->mkSort("T");
    Type* booleanType = d_nodeManager->booleanType();
    Type* predType = d_nodeManager->mkFunctionType(sort, booleanType);

    Node f = d_nodeManager->mkVar(predType);
    Node a = d_nodeManager->mkVar(booleanType);
    Node fa = d_nodeManager->mkNode(kind::APPLY_UF, f, a);

    TS_ASSERT( fa.hasOperator() );
    TS_ASSERT( !f.hasOperator() );
    TS_ASSERT( !a.hasOperator() );

    TS_ASSERT( fa.getNumChildren() == 1 );
    TS_ASSERT( f.getNumChildren() == 0 );
    TS_ASSERT( a.getNumChildren() == 0 );

    TS_ASSERT( f == fa.getOperator() );
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( f.getOperator(), AssertionException );
    TS_ASSERT_THROWS( a.getOperator(), AssertionException );
#endif /* CVC4_ASSERTIONS */
  }

  void testNaryExpForSize(Kind k, int N) {
    NodeBuilder<> nbz(k);
    Node trueNode = d_nodeManager->mkConst(true);
    for(int i = 0; i < N; ++i) {
      nbz << trueNode;
    }
    Node result = nbz;
    TS_ASSERT( N == result.getNumChildren() );
  }

  void testNumChildren() {
    /*inline size_t getNumChildren() const;*/

    Node trueNode = d_nodeManager->mkConst(true);

    //test 0
    TS_ASSERT(0 == (Node::null()).getNumChildren());

    //test 1
    TS_ASSERT(1 == trueNode.notNode().getNumChildren());

    //test 2
    TS_ASSERT(2 == trueNode.andNode(trueNode).getNumChildren());

    //Bigger tests

    srand(0);
    int trials = 500;
    for(int i = 0; i < trials; ++i) {
      int N = rand() % 1000 + 2;
      testNaryExpForSize(AND, N);
    }

#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS( testNaryExpForSize(AND, 0), AssertionException );
    TS_ASSERT_THROWS( testNaryExpForSize(AND, 1), AssertionException );
    TS_ASSERT_THROWS( testNaryExpForSize(NOT, 0), AssertionException );
    TS_ASSERT_THROWS( testNaryExpForSize(NOT, 2), AssertionException );
#endif /* CVC4_ASSERTIONS */
  }

  void testIterator() {
    NodeBuilder<> b;
    Node x = d_nodeManager->mkVar(d_booleanType);
    Node y = d_nodeManager->mkVar(d_booleanType);
    Node z = d_nodeManager->mkVar(d_booleanType);
    Node n = b << x << y << z << kind::AND;

    { // iterator
      Node::iterator i = n.begin();
      TS_ASSERT(*i++ == x);
      TS_ASSERT(*i++ == y);
      TS_ASSERT(*i++ == z);
      TS_ASSERT(i == n.end());
    }

    { // same for const iterator
      const Node& c = n;
      Node::const_iterator i = c.begin();
      TS_ASSERT(*i++ == x);
      TS_ASSERT(*i++ == y);
      TS_ASSERT(*i++ == z);
      TS_ASSERT(i == n.end());
    }
  }

  void testToString() {
    Type* booleanType = d_nodeManager->booleanType();

    Node w = d_nodeManager->mkVar(booleanType, "w");
    Node x = d_nodeManager->mkVar(booleanType, "x");
    Node y = d_nodeManager->mkVar(booleanType, "y");
    Node z = d_nodeManager->mkVar(booleanType, "z");
    Node m = NodeBuilder<>() << w << x << kind::OR;
    Node n = NodeBuilder<>() << m << y << z << kind::AND;

    TS_ASSERT(n.toString() == "(AND (OR w x) y z)");
  }

  void testToStream() {
    Type* booleanType = d_nodeManager->booleanType();

    Node w = d_nodeManager->mkVar(booleanType, "w");
    Node x = d_nodeManager->mkVar(booleanType, "x");
    Node y = d_nodeManager->mkVar(booleanType, "y");
    Node z = d_nodeManager->mkVar(booleanType, "z");
    Node m = NodeBuilder<>() << x << y << kind::OR;
    Node n = NodeBuilder<>() << w << m << z << kind::AND;
    Node o = NodeBuilder<>() << n << n << kind::XOR;

    stringstream sstr;
    n.toStream(sstr);
    TS_ASSERT(sstr.str() == "(AND w (OR x y) z)");

    sstr.str(string());
    o.toStream(sstr);
    TS_ASSERT(sstr.str() == "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");

    sstr.str(string());
    sstr << n;
    TS_ASSERT(sstr.str() == "(AND w (OR x y) z)");

    sstr.str(string());
    sstr << o;
    TS_ASSERT(sstr.str() == "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");

    sstr.str(string());
    sstr << Node::setdepth(0) << n;
    TS_ASSERT(sstr.str() == "(AND w (OR x y) z)");

    sstr.str(string());
    sstr << Node::setdepth(0) << o;
    TS_ASSERT(sstr.str() == "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");

    sstr.str(string());
    sstr << Node::setdepth(1) << n;
    TS_ASSERT(sstr.str() == "(AND w (OR (...) (...)) z)");

    sstr.str(string());
    sstr << Node::setdepth(1) << o;
    TS_ASSERT(sstr.str() == "(XOR (AND (...) (...) (...)) (AND (...) (...) (...)))");

    sstr.str(string());
    sstr << Node::setdepth(2) << n;
    TS_ASSERT(sstr.str() == "(AND w (OR x y) z)");

    sstr.str(string());
    sstr << Node::setdepth(2) << o;
    TS_ASSERT(sstr.str() == "(XOR (AND w (OR (...) (...)) z) (AND w (OR (...) (...)) z))");

    sstr.str(string());
    sstr << Node::setdepth(3) << n;
    TS_ASSERT(sstr.str() == "(AND w (OR x y) z)");

    sstr.str(string());
    sstr << Node::setdepth(3) << o;
    TS_ASSERT(sstr.str() == "(XOR (AND w (OR x y) z) (AND w (OR x y) z))");
  }
};
