/*********************                                                        */
/*! \file node_traversal_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of node traversal iterators.
 **/

#include <cxxtest/TestSuite.h>

// Used in some of the tests
#include <algorithm>
#include <cstddef>
#include <iterator>
#include <sstream>
#include <string>
#include <vector>

#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_traversal.h"
#include "expr/node_value.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class NodePostorderTraversalBlack : public CxxTest::TestSuite
{
 private:
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

 public:
  void setUp() override
  {
    d_nodeManager = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_nodeManager;
  }

  void testPreincrementIteration()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    auto traversal = NodeDfsIterable(cnd, VisitOrder::POSTORDER);
    NodeDfsIterator i = traversal.begin();
    NodeDfsIterator end = traversal.end();
    TS_ASSERT_EQUALS(*i, tb);
    TS_ASSERT_DIFFERS(i, end);
    ++i;
    TS_ASSERT_EQUALS(*i, eb);
    TS_ASSERT_DIFFERS(i, end);
    ++i;
    TS_ASSERT_EQUALS(*i, cnd);
    TS_ASSERT_DIFFERS(i, end);
    ++i;
    TS_ASSERT_EQUALS(i, end);
  }

  void testPostincrementIteration()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    auto traversal = NodeDfsIterable(cnd, VisitOrder::POSTORDER);
    NodeDfsIterator i = traversal.begin();
    NodeDfsIterator end = traversal.end();
    TS_ASSERT_EQUALS(*(i++), tb);
    TS_ASSERT_EQUALS(*(i++), eb);
    TS_ASSERT_EQUALS(*(i++), cnd);
    TS_ASSERT_EQUALS(i, end);
  }

  void testPostorderIsDefault()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    auto traversal = NodeDfsIterable(cnd);
    NodeDfsIterator i = traversal.begin();
    NodeDfsIterator end = traversal.end();
    TS_ASSERT_EQUALS(*i, tb);
    TS_ASSERT_DIFFERS(i, end);
  }

  void testRangeForLoop()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    size_t count = 0;
    for (auto i : NodeDfsIterable(cnd, VisitOrder::POSTORDER))
    {
      ++count;
    }
    TS_ASSERT_EQUALS(count, 3);
  }

  void testCountIfWithLoop()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    size_t count = 0;
    for (auto i : NodeDfsIterable(cnd, VisitOrder::POSTORDER))
    {
      if (i.isConst())
      {
        ++count;
      }
    }
    TS_ASSERT_EQUALS(count, 2);
  }

  void testStlCountIf()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);

    auto traversal = NodeDfsIterable(top, VisitOrder::POSTORDER);

    size_t count = std::count_if(traversal.begin(),
                                 traversal.end(),
                                 [](TNode n) { return n.isConst(); });
    TS_ASSERT_EQUALS(count, 2);
  }

  void testStlCopy()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
    std::vector<TNode> expected = {tb, eb, cnd, top};

    auto traversal = NodeDfsIterable(top, VisitOrder::POSTORDER);

    std::vector<TNode> actual;
    std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
    TS_ASSERT_EQUALS(actual, expected);
  }

  void testSkipIf()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
    std::vector<TNode> expected = {top};

    auto traversal = NodeDfsIterable(
        top, VisitOrder::POSTORDER, [&cnd](TNode n) { return n == cnd; });

    std::vector<TNode> actual;
    std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
    TS_ASSERT_EQUALS(actual, expected);
  }

  void testSkipAll()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
    std::vector<TNode> expected = {};

    auto traversal = NodeDfsIterable(top, VisitOrder::POSTORDER,
        [](TNode n) { return true; });

    std::vector<TNode> actual;
    std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
    TS_ASSERT_EQUALS(actual, expected);
  }
};

class NodePreorderTraversalBlack : public CxxTest::TestSuite
{
 private:
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

 public:
  void setUp() override
  {
    d_nodeManager = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_nodeManager;
  }

  void testPreincrementIteration()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    auto traversal = NodeDfsIterable(cnd, VisitOrder::PREORDER);
    NodeDfsIterator i = traversal.begin();
    NodeDfsIterator end = traversal.end();
    TS_ASSERT_EQUALS(*i, cnd);
    TS_ASSERT_DIFFERS(i, end);
    ++i;
    TS_ASSERT_EQUALS(*i, tb);
    TS_ASSERT_DIFFERS(i, end);
    ++i;
    TS_ASSERT_EQUALS(*i, eb);
    TS_ASSERT_DIFFERS(i, end);
    ++i;
    TS_ASSERT_EQUALS(i, end);
  }

  void testPostincrementIteration()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    auto traversal = NodeDfsIterable(cnd, VisitOrder::PREORDER);
    NodeDfsIterator i = traversal.begin();
    NodeDfsIterator end = traversal.end();
    TS_ASSERT_EQUALS(*(i++), cnd);
    TS_ASSERT_EQUALS(*(i++), tb);
    TS_ASSERT_EQUALS(*(i++), eb);
    TS_ASSERT_EQUALS(i, end);
  }

  void testRangeForLoop()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    size_t count = 0;
    for (auto i : NodeDfsIterable(cnd, VisitOrder::PREORDER))
    {
      ++count;
    }
    TS_ASSERT_EQUALS(count, 3);
  }

  void testCountIfWithLoop()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    size_t count = 0;
    for (auto i : NodeDfsIterable(cnd, VisitOrder::PREORDER))
    {
      if (i.isConst())
      {
        ++count;
      }
    }
    TS_ASSERT_EQUALS(count, 2);
  }

  void testStlCountIf()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);

    auto traversal = NodeDfsIterable(top, VisitOrder::PREORDER);

    size_t count = std::count_if(traversal.begin(),
                                 traversal.end(),
                                 [](TNode n) { return n.isConst(); });
    TS_ASSERT_EQUALS(count, 2);
  }

  void testStlCopy()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
    std::vector<TNode> expected = {top, cnd, tb, eb};

    auto traversal = NodeDfsIterable(top, VisitOrder::PREORDER);

    std::vector<TNode> actual;
    std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
    TS_ASSERT_EQUALS(actual, expected);
  }

  void testSkipIf()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
    std::vector<TNode> expected = {top, cnd, eb};

    auto traversal = NodeDfsIterable(
        top, VisitOrder::PREORDER, [&tb](TNode n) { return n == tb; });

    std::vector<TNode> actual;
    std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
    TS_ASSERT_EQUALS(actual, expected);
  }
};
