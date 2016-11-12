/*********************                                                        */
/*! \file node_manager_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::NodeManager.
 **
 ** White box testing of CVC4::NodeManager.
 **/

#include <cxxtest/TestSuite.h>

#include <string>
#include <vector>

#include "base/output.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;

class NodeManagerBlack : public CxxTest::TestSuite {

  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_nodeManager = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() {
    delete d_scope;
    delete d_nodeManager;
  }

  void testMkNodeNot() {
    Node x = d_nodeManager->mkSkolem("x",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(NOT, x);
    TS_ASSERT_EQUALS( n.getNumChildren(), 1u );
    TS_ASSERT_EQUALS( n.getKind(), NOT);
    TS_ASSERT_EQUALS( n[0], x);
  }

  void testMkNodeBinary() {
    Node x = d_nodeManager->mkSkolem("x",d_nodeManager->booleanType());
    Node y = d_nodeManager->mkSkolem("y",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(IMPLIES, x, y);
    TS_ASSERT_EQUALS( n.getNumChildren(), 2u );
    TS_ASSERT_EQUALS( n.getKind(), IMPLIES);
    TS_ASSERT_EQUALS( n[0], x);
    TS_ASSERT_EQUALS( n[1], y);
  }

  void testMkNodeThreeChildren() {
    Node x = d_nodeManager->mkSkolem("x",d_nodeManager->booleanType());
    Node y = d_nodeManager->mkSkolem("y",d_nodeManager->booleanType());
    Node z = d_nodeManager->mkSkolem("z",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x, y, z);
    TS_ASSERT_EQUALS( n.getNumChildren(), 3u );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x);
    TS_ASSERT_EQUALS( n[1], y);
    TS_ASSERT_EQUALS( n[2], z);
  }

  void testMkNodeFourChildren() {
    Node x1 = d_nodeManager->mkSkolem("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkSkolem("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkSkolem("x3",d_nodeManager->booleanType());
    Node x4 = d_nodeManager->mkSkolem("x4",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4);
    TS_ASSERT_EQUALS( n.getNumChildren(), 4u );
    TS_ASSERT_EQUALS( n.getKind(), AND );
    TS_ASSERT_EQUALS( n[0], x1 );
    TS_ASSERT_EQUALS( n[1], x2 );
    TS_ASSERT_EQUALS( n[2], x3 );
    TS_ASSERT_EQUALS( n[3], x4 );
  }

  void testMkNodeFiveChildren() {
    Node x1 = d_nodeManager->mkSkolem("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkSkolem("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkSkolem("x3",d_nodeManager->booleanType());
    Node x4 = d_nodeManager->mkSkolem("x4",d_nodeManager->booleanType());
    Node x5 = d_nodeManager->mkSkolem("x5",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(AND, x1, x2, x3, x4, x5);
    TS_ASSERT_EQUALS( n.getNumChildren(), 5u );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    TS_ASSERT_EQUALS( n[0], x1);
    TS_ASSERT_EQUALS( n[1], x2);
    TS_ASSERT_EQUALS( n[2], x3);
    TS_ASSERT_EQUALS( n[3], x4);
    TS_ASSERT_EQUALS( n[4], x5);
  }

  void testMkNodeVectorOfNodeChildren() {
    Node x1 = d_nodeManager->mkSkolem("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkSkolem("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkSkolem("x3",d_nodeManager->booleanType());
    std::vector<Node> args;
    args.push_back(x1);
    args.push_back(x2);
    args.push_back(x3);
    Node n = d_nodeManager->mkNode(AND, args);
    TS_ASSERT_EQUALS( n.getNumChildren(), args.size() );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    for( unsigned i = 0; i < args.size(); ++i ) {
      TS_ASSERT_EQUALS( n[i], args[i]);
    }
  }

  void testMkNodeVectorOfTNodeChildren() {
    Node x1 = d_nodeManager->mkSkolem("x1",d_nodeManager->booleanType());
    Node x2 = d_nodeManager->mkSkolem("x2",d_nodeManager->booleanType());
    Node x3 = d_nodeManager->mkSkolem("x3",d_nodeManager->booleanType());
    std::vector<TNode> args;
    args.push_back(x1);
    args.push_back(x2);
    args.push_back(x3);
    Node n = d_nodeManager->mkNode(AND, args);
    TS_ASSERT_EQUALS( n.getNumChildren(), args.size() );
    TS_ASSERT_EQUALS( n.getKind(), AND);
    for( unsigned i = 0; i < args.size(); ++i ) {
      TS_ASSERT_EQUALS( n[i], args[i]);
    }
  }

  void testMkVarWithName() {
    TypeNode booleanType = d_nodeManager->booleanType();
    Node x = d_nodeManager->mkSkolem("x", booleanType, "", NodeManager::SKOLEM_EXACT_NAME);
    TS_ASSERT_EQUALS(x.getKind(),SKOLEM);
    TS_ASSERT_EQUALS(x.getNumChildren(),0u);
    TS_ASSERT_EQUALS(x.getAttribute(VarNameAttr()),"x");
    TS_ASSERT_EQUALS(x.getType(),booleanType);
  }

  void testMkConstBool() {
    Node tt = d_nodeManager->mkConst(true);
    TS_ASSERT_EQUALS(tt.getConst<bool>(),true);
    Node ff = d_nodeManager->mkConst(false);
    TS_ASSERT_EQUALS(ff.getConst<bool>(),false);
  }

  void testMkConstRat() {
    Rational r("3/2");
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
    TypeNode t = d_nodeManager->booleanType();
    TypeNode t2 = d_nodeManager->booleanType();
    TypeNode t3 = d_nodeManager->mkSort("T");
    TS_ASSERT( t.isBoolean() );
    TS_ASSERT( !t.isFunction() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );
    TS_ASSERT_EQUALS(t, t2);
    TS_ASSERT( t != t3 );

    TypeNode bt = t;
    TS_ASSERT_EQUALS( bt, t);
  }

  void testMkFunctionTypeBoolToBool() {
    TypeNode booleanType = d_nodeManager->booleanType();
    TypeNode t = d_nodeManager->mkFunctionType(booleanType,booleanType);
    TypeNode t2 = d_nodeManager->mkFunctionType(booleanType,booleanType);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    TypeNode ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), 1u);
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], booleanType);
    TS_ASSERT_EQUALS(ft.getRangeType(), booleanType);

  }

  void testMkFunctionTypeVectorOfArgsWithReturnType() {
    TypeNode a = d_nodeManager->mkSort();
    TypeNode b = d_nodeManager->mkSort();
    TypeNode c = d_nodeManager->mkSort();

    std::vector<TypeNode> argTypes;
    argTypes.push_back(a);
    argTypes.push_back(b);

    TypeNode t = d_nodeManager->mkFunctionType(argTypes,c);
    TypeNode t2 = d_nodeManager->mkFunctionType(argTypes,c);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    TypeNode ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), argTypes.size());
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft.getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft.getRangeType(), c);

  }

  void testMkFunctionTypeVectorOfArguments() {
    TypeNode a = d_nodeManager->mkSort();
    TypeNode b = d_nodeManager->mkSort();
    TypeNode c = d_nodeManager->mkSort();

    std::vector<TypeNode> types;
    types.push_back(a);
    types.push_back(b);
    types.push_back(c);

    TypeNode t = d_nodeManager->mkFunctionType(types);
    TypeNode t2 = d_nodeManager->mkFunctionType(types);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( !t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    TypeNode ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), types.size()-1);
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft.getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft.getRangeType(), c);
  }

  void testMkPredicateType() {
    TypeNode a = d_nodeManager->mkSort("a");
    TypeNode b = d_nodeManager->mkSort("b");
    TypeNode c = d_nodeManager->mkSort("c");
    TypeNode booleanType = d_nodeManager->booleanType();

    std::vector<TypeNode> argTypes;
    argTypes.push_back(a);
    argTypes.push_back(b);
    argTypes.push_back(c);

    TypeNode t = d_nodeManager->mkPredicateType(argTypes);
    TypeNode t2 = d_nodeManager->mkPredicateType(argTypes);

    TS_ASSERT( !t.isBoolean() );
    TS_ASSERT( t.isFunction() );
    TS_ASSERT( !t.isNull() );
    TS_ASSERT( t.isPredicate() );
    TS_ASSERT( !t.isSort() );

    TS_ASSERT_EQUALS( t, t2 );

    TypeNode ft = t;
    TS_ASSERT_EQUALS( ft, t );
    TS_ASSERT_EQUALS(ft.getArgTypes().size(), argTypes.size());
    TS_ASSERT_EQUALS(ft.getArgTypes()[0], a);
    TS_ASSERT_EQUALS(ft.getArgTypes()[1], b);
    TS_ASSERT_EQUALS(ft.getArgTypes()[2], c);
    TS_ASSERT_EQUALS(ft.getRangeType(), booleanType);

  }

  /* This test is only valid if assertions are enabled. */
  void testMkNodeTooFew() {
#ifdef CVC4_ASSERTIONS
    Node x = d_nodeManager->mkSkolem( "x", d_nodeManager->booleanType() );
    TS_ASSERT_THROWS( d_nodeManager->mkNode(AND, x), AssertionException );
#endif
  }

  /* This test is only valid if assertions are enabled. */
  void testMkNodeTooMany() {
#ifdef CVC4_ASSERTIONS
    std::vector<Node> vars;
    const unsigned int max = metakind::getUpperBoundForKind(AND);
    TypeNode boolType = d_nodeManager->booleanType();
    Node skolem_i = d_nodeManager->mkSkolem("i", boolType);
    Node skolem_j = d_nodeManager->mkSkolem("j", boolType);
    Node andNode = skolem_i.andNode(skolem_j);
    Node orNode = skolem_i.orNode(skolem_j);
    while (vars.size() <= max) {
      vars.push_back(andNode);
      vars.push_back(skolem_j);
      vars.push_back(orNode);
    }
    TS_ASSERT_THROWS(d_nodeManager->mkNode(AND, vars), AssertionException);
#endif
  }
};
