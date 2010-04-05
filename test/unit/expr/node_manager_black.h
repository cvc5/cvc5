/*********************                                                        */
/** node_manager_black.h
 ** Original author: 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::NodeManager.
 **/

#include <cxxtest/TestSuite.h>

#include <string>
#include <vector>

#include "expr/node_manager.h"
#include "context/context.h"

#include "util/rational.h"
#include "util/integer.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;
using namespace CVC4::context;

class NodeManagerBlack : public CxxTest::TestSuite {

  Context* d_context;
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_context = new Context;
    d_nodeManager = new NodeManager(d_context);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() {
    delete d_scope;
    delete d_nodeManager;
    delete d_context;
  }

  void testMkNode1() {
    Node x = d_nodeManager->mkVar("x",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(NOT, x);
    TS_ASSERT_EQUALS( n.getNumChildren(), 1 );
    TS_ASSERT_EQUALS( n.getKind(), NOT);
    TS_ASSERT_EQUALS( n[0], x);
  }

  void testMkNode2() {
    Node x = d_nodeManager->mkVar("x",d_nodeManager->booleanType());
    Node y = d_nodeManager->mkVar("y",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(IMPLIES, x, y);
    TS_ASSERT_EQUALS( n.getNumChildren(), 2 );
    TS_ASSERT_EQUALS( n.getKind(), IMPLIES);
    TS_ASSERT_EQUALS( n[0], x);
    TS_ASSERT_EQUALS( n[1], y);
  }

  void testMkNode3() {
    Node x = d_nodeManager->mkVar("x",d_nodeManager->booleanType());
    Node y = d_nodeManager->mkVar("y",d_nodeManager->booleanType());
    Node z = d_nodeManager->mkVar("z",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x, y, z);
    TS_ASSERT_EQUALS( n.getNumChildren(), 3 );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x);
    TS_ASSERT_EQUALS( n[1], y);
    TS_ASSERT_EQUALS( n[2], z);
  }

  void testMkNode4() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    Node x4 = d_nodeManager->mkVar("x4",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4);
    TS_ASSERT_EQUALS( n.getNumChildren(), 4 );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x1);
    TS_ASSERT_EQUALS( n[1], x2);
    TS_ASSERT_EQUALS( n[2], x3);
    TS_ASSERT_EQUALS( n[3], x4);
  }

  void testMkNode5() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    Node x4 = d_nodeManager->mkVar("x4",d_nodeManager->booleanType());
    Node x5 = d_nodeManager->mkVar("x5",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4, x5);
    TS_ASSERT_EQUALS( n.getNumChildren(), 5 );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x1);
    TS_ASSERT_EQUALS( n[1], x2);
    TS_ASSERT_EQUALS( n[2], x3);
    TS_ASSERT_EQUALS( n[3], x4);
    TS_ASSERT_EQUALS( n[4], x5);
  }

  void testMkNodeVecOfNode() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    std::vector<Node> args;
    args.push_back(x1);
    args.push_back(x2);
    args.push_back(x3);
    Node n = d_nodeManager->mkNode(AND, args);
    TS_ASSERT_EQUALS( n.getNumChildren(), args.size() );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    for( int i=0; i < args.size(); ++i ) {
      TS_ASSERT_EQUALS( n[i], args[i]);
    }
  }

  void testMkNodeVecOfTNode() {
    Node x1 = d_nodeManager->mkVar("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkVar("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkVar("x3",d_nodeManager->booleanType());
    std::vector<TNode> args;
    args.push_back(x1);
    args.push_back(x2);
    args.push_back(x3);
    Node n = d_nodeManager->mkNode(AND, args);
    TS_ASSERT_EQUALS( n.getNumChildren(), args.size() );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    for( int i=0; i < args.size(); ++i ) {
      TS_ASSERT_EQUALS( n[i], args[i]);
    }
  }

  void testMkVar1() {
    Type* booleanType = d_nodeManager->booleanType();
    Node x = d_nodeManager->mkVar(booleanType);
    TS_ASSERT_EQUALS(x.getKind(),VARIABLE);
    TS_ASSERT_EQUALS(x.getNumChildren(),0);
    TS_ASSERT_EQUALS(x.getType(),booleanType);
  }

  void testMkVar2() {
    Type* booleanType = d_nodeManager->booleanType();
    Node x = d_nodeManager->mkVar("x", booleanType);
    TS_ASSERT_EQUALS(x.getKind(),VARIABLE);
    TS_ASSERT_EQUALS(x.getNumChildren(),0);
    TS_ASSERT_EQUALS(x.getAttribute(VarNameAttr()),"x");
    TS_ASSERT_EQUALS(x.getType(),booleanType);
  }

  void testMkConstBool() {
    Node tt = d_nodeManager->mkConst(true);
    TS_ASSERT_EQUALS(tt.getConst<bool>(),true);
    Node ff = d_nodeManager->mkConst(false);
    TS_ASSERT_EQUALS(ff.getConst<bool>(),false);
  }


  void testMkConstInt() {
    Integer i = "3";
    Node n = d_nodeManager->mkConst(i);
    TS_ASSERT_EQUALS(n.getConst<Integer>(),i);
  }

  void testMkConstRat() {
    Rational r = "3/2";
    Node n = d_nodeManager->mkConst(r);
    TS_ASSERT_EQUALS(n.getConst<Rational>(),r);
  }

  void testHasOperator() {
    TS_ASSERT( NodeManager::hasOperator(AND) );
    TS_ASSERT( NodeManager::hasOperator(OR) );
    TS_ASSERT( NodeManager::hasOperator(NOT) );
    TS_ASSERT( NodeManager::hasOperator(APPLY_UF) );
    TS_ASSERT( !NodeManager::hasOperator(VARIABLE) );
  }

  void testBooleanType() {
    Type* booleanType1 = d_nodeManager->booleanType();
    Type* booleanType2 = d_nodeManager->booleanType();
    Type* otherType = d_nodeManager->mkSort("T");
    TS_ASSERT( booleanType1->isBoolean() );
    TS_ASSERT_EQUALS(booleanType1, booleanType2);
    TS_ASSERT( booleanType1 != otherType );
  }

  void testKindType() {
    Type* kindType1 = d_nodeManager->kindType();
    Type* kindType2 = d_nodeManager->kindType();
    Type* otherType = d_nodeManager->mkSort("T");
    TS_ASSERT( kindType1->isKind() );
    TS_ASSERT_EQUALS(kindType1, kindType2);
    TS_ASSERT( kindType1 != otherType );
    // TODO: Is there a way to get the type of otherType (it should == kindType)
  }

  /* TODO: All of the type comparisons in all of the following tests are
   * strictly for pointer equality. This is too weak for disequalities and
   * too strong for equalities! Also, it means we can't really check for
   * structural equality between two identical calls to mkFunctionType (see
   * the commented out assertions at the bottom of each test). Unfortunately,
   * with the current type implementation it's the best we can do. */

  void testMkFunctionType2() {
    Type *booleanType = d_nodeManager->booleanType();
    Type *t = d_nodeManager->mkFunctionType(booleanType,booleanType);
    TS_ASSERT( t != booleanType );
    TS_ASSERT( t->isFunction() );

    FunctionType* ft = (FunctionType*)t;
    TS_ASSERT_EQUALS(ft->getArgTypes().size(), 1);
    TS_ASSERT_EQUALS(ft->getArgTypes()[0], booleanType);
    TS_ASSERT_EQUALS(ft->getRangeType(), booleanType);

/*    Type *t2 = d_nodeManager->mkFunctionType(booleanType,booleanType);
    TS_ASSERT_EQUALS( t, t2 );*/
  }

  void testMkFunctionTypeVecType() {
    Type *a = d_nodeManager->mkSort("a");
    Type *b = d_nodeManager->mkSort("b");
    Type *c = d_nodeManager->mkSort("c");

    std::vector<Type*> argTypes;
    argTypes.push_back(a);
    argTypes.push_back(b);

    Type *t = d_nodeManager->mkFunctionType(argTypes,c);

    TS_ASSERT( t != a );
    TS_ASSERT( t != b );
    TS_ASSERT( t != c );
    TS_ASSERT( t->isFunction() );

    FunctionType* ft = (FunctionType*)t;
    TS_ASSERT_EQUALS(ft->getArgTypes().size(), argTypes.size());
    TS_ASSERT_EQUALS(ft->getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft->getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft->getRangeType(), c);

/*    Type *t2 = d_nodeManager->mkFunctionType(argTypes,c);
    TS_ASSERT_EQUALS( t, t2 );*/
  }

  void testMkFunctionTypeVec() {
    Type *a = d_nodeManager->mkSort("a");
    Type *b = d_nodeManager->mkSort("b");
    Type *c = d_nodeManager->mkSort("c");

    std::vector<Type*> types;
    types.push_back(a);
    types.push_back(b);
    types.push_back(c);

    Type *t = d_nodeManager->mkFunctionType(types);

    TS_ASSERT( t != a );
    TS_ASSERT( t != b );
    TS_ASSERT( t != c );
    TS_ASSERT( t->isFunction() );

    FunctionType* ft = (FunctionType*)t;
    TS_ASSERT_EQUALS(ft->getArgTypes().size(), types.size()-1);
    TS_ASSERT_EQUALS(ft->getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft->getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft->getRangeType(), c);

/*    Type *t2 = d_nodeManager->mkFunctionType(types);
    TS_ASSERT_EQUALS( t, t2 );*/
  }

  void testMkPredicateType() {
    Type *a = d_nodeManager->mkSort("a");
    Type *b = d_nodeManager->mkSort("b");
    Type *c = d_nodeManager->mkSort("c");
    Type *booleanType = d_nodeManager->booleanType();

    std::vector<Type*> argTypes;
    argTypes.push_back(a);
    argTypes.push_back(b);
    argTypes.push_back(c);

    Type *t = d_nodeManager->mkPredicateType(argTypes);

    TS_ASSERT( t != a );
    TS_ASSERT( t != b );
    TS_ASSERT( t != c );
    TS_ASSERT( t != booleanType );
    TS_ASSERT( t->isFunction() );

    FunctionType* ft = (FunctionType*)t;
    TS_ASSERT_EQUALS(ft->getArgTypes().size(), argTypes.size());
    TS_ASSERT_EQUALS(ft->getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft->getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft->getArgTypes()[2], c);
    TS_ASSERT_EQUALS(ft->getRangeType(), booleanType);

//    Type *t2 = d_nodeManager->mkPredicateType(argTypes);
//    TS_ASSERT_EQUALS( t, t2 );
  }
};
