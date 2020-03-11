/*********************                                                        */
/*! \file node_traversal_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of note traversal iterators.
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
#include "expr/node_value.h"
#include "smt_util/node_traversal.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

class NodeBlack : public CxxTest::TestSuite
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

    auto traversal = NodePostorderIterable(cnd);
    NodePostorderIterator i = traversal.begin();
    NodePostorderIterator end = traversal.end();
    TS_ASSERT(*i == tb);
    TS_ASSERT(i != end);
    ++i;
    TS_ASSERT(*i == eb);
    TS_ASSERT(i != end);
    ++i;
    TS_ASSERT(*i == cnd);
    TS_ASSERT(i != end);
    ++i;
    TS_ASSERT(i == end);
  }

  void testPostincrementIteration()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    NodePostorderIterator i = NodePostorderIterable(cnd).begin();
    NodePostorderIterator end = NodePostorderIterable(cnd).end();
    TS_ASSERT(*(i++) == tb);
    TS_ASSERT(*(i++) == eb);
    TS_ASSERT(*(i++) == cnd);
    TS_ASSERT(i == end);
  }

  void testRangeForLoop()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    size_t count = 0;
    for (auto i : NodePostorderIterable(cnd))
    {
      ++count;
    }
    TS_ASSERT(count == 3);
  }

  void testCountIfWithLoop()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);

    size_t count = 0;
    for (auto i : NodePostorderIterable(cnd))
    {
      if (i.isConst())
      {
        ++count;
      }
    }
    TS_ASSERT(count == 2);
  }

  void testStlCountIf()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);

    auto traversal = NodePostorderIterable(top);

    size_t count = std::count_if(traversal.begin(),
                                 traversal.end(),
                                 [](TNode n) { return n.isConst(); });
    TS_ASSERT(count == 2);
  }

  void testStlCopy()
  {
    Node tb = d_nodeManager->mkConst(true);
    Node eb = d_nodeManager->mkConst(false);
    Node cnd = d_nodeManager->mkNode(XOR, tb, eb);
    Node top = d_nodeManager->mkNode(XOR, cnd, cnd);
    std::vector<TNode> expected = {tb, eb, cnd, top};

    auto traversal = NodePostorderIterable(top);

    std::vector<TNode> actual;
    std::copy(traversal.begin(), traversal.end(), std::back_inserter(actual));
    TS_ASSERT(actual == expected);
  }
};
