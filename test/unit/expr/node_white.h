/*********************                                                        */
/*! \file node_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::Node.
 **
 ** White box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

#include <string>

#include "base/check.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::expr;
using namespace std;

class NodeWhite : public CxxTest::TestSuite {

  NodeManager* d_nm;
  NodeManagerScope* d_scope;

 public:
  void setUp() override
  {
    d_nm = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_nm;
  }

  void testNull() {
    TS_ASSERT_EQUALS(Node::null(), Node::s_null);
  }

  void testCopyCtor() {
    Node e(Node::s_null);
  }

  void testBuilder() {
    NodeBuilder<> b;
    TS_ASSERT(b.d_nv->getId() == 0);
    TS_ASSERT(b.d_nv->getKind() == UNDEFINED_KIND);
    TS_ASSERT_EQUALS(b.d_nv->d_nchildren, 0u);
    /* etc. */
  }

  void testIterators() {
    Node x = d_nm->mkVar("x", d_nm->integerType());
    Node y = d_nm->mkVar("y", d_nm->integerType());
    Node x_plus_y = d_nm->mkNode(PLUS, x, y);
    Node two = d_nm->mkConst(Rational(2));
    Node x_times_2 = d_nm->mkNode(MULT, x, two);

    Node n = d_nm->mkNode(PLUS, x_times_2, x_plus_y, y);

    Node::iterator i;

    i = find(n.begin(), n.end(), x_plus_y);
    TS_ASSERT(i != n.end());
    TS_ASSERT(*i == x_plus_y);

    i = find(n.begin(), n.end(), x);
    TS_ASSERT(i == n.end());

    i = find(x_times_2.begin(), x_times_2.end(), two);
    TS_ASSERT(i != x_times_2.end());
    TS_ASSERT(*i == two);

    i = find(n.begin(), n.end(), y);
    TS_ASSERT(i != n.end());
    TS_ASSERT(*i == y);

    vector<Node> v;
    copy(n.begin(), n.end(), back_inserter(v));
    TS_ASSERT(n.getNumChildren() == v.size());
    TS_ASSERT(3 == v.size());
    TS_ASSERT(v[0] == x_times_2);
    TS_ASSERT(v[1] == x_plus_y);
    TS_ASSERT(v[2] == y);
  }
};
