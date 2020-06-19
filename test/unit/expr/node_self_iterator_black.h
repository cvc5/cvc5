/*********************                                                        */
/*! \file node_self_iterator_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::expr::NodeSelfIterator
 **
 ** Black box testing of CVC4::expr::NodeSelfIterator
 **/

#include <cxxtest/TestSuite.h>

#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "expr/node_builder.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::expr;
using namespace std;

class NodeSelfIteratorBlack : public CxxTest::TestSuite {
private:

  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;
  TypeNode* d_booleanType;
  TypeNode* d_realType;

 public:
  void setUp() override
  {
    d_nodeManager = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
    d_booleanType = new TypeNode(d_nodeManager->booleanType());
    d_realType = new TypeNode(d_nodeManager->realType());
  }

  void tearDown() override
  {
    delete d_booleanType;
    delete d_scope;
    delete d_nodeManager;
  }

  void testSelfIteration() {
    Node x = d_nodeManager->mkSkolem("x", *d_booleanType);
    Node y = d_nodeManager->mkSkolem("y", *d_booleanType);
    Node x_and_y = x.andNode(y);
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
