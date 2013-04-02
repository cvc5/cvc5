/*********************                                                        */
/*! \file node_self_iterator_black.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::expr::NodeSelfIterator
 **
 ** Black box testing of CVC4::expr::NodeSelfIterator
 **/

#include <cxxtest/TestSuite.h>

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "expr/node_builder.h"
#include "expr/convenience_node_builders.h"

using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::kind;
using namespace CVC4::expr;
using namespace std;

class NodeSelfIteratorBlack : public CxxTest::TestSuite {
private:

  Context* d_ctxt;
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;
  TypeNode* d_booleanType;
  TypeNode* d_realType;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nodeManager = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
    d_booleanType = new TypeNode(d_nodeManager->booleanType());
    d_realType = new TypeNode(d_nodeManager->realType());
  }

  void tearDown() {
    delete d_booleanType;
    delete d_scope;
    delete d_nodeManager;
    delete d_ctxt;
  }

  void testSelfIteration() {
    Node x = d_nodeManager->mkSkolem("x", *d_booleanType);
    Node y = d_nodeManager->mkSkolem("y", *d_booleanType);
    Node x_and_y = x && y;
    NodeSelfIterator i = x_and_y, j = NodeSelfIterator::self(x_and_y);
    TS_ASSERT(i != x_and_y.end());
    TS_ASSERT(j != x_and_y.end());
    TS_ASSERT(*i == x_and_y);
    TS_ASSERT(*j == x_and_y);
    TS_ASSERT(*i++ == x_and_y);
    TS_ASSERT(*j++ == x_and_y);
    TS_ASSERT(i == NodeSelfIterator::selfEnd(x_and_y));
    TS_ASSERT(j == NodeSelfIterator::selfEnd(x_and_y));
    TS_ASSERT(i == x_and_y.end());
    TS_ASSERT(j == x_and_y.end());

    i = x_and_y.begin();
    TS_ASSERT(i != x_and_y.end());
    TS_ASSERT(*i == x);
    TS_ASSERT(*++i == y);
    TS_ASSERT(++i == x_and_y.end());
  }

};
