/*********************                                                        */
/*! \file node_manager_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
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

#include "expr/node_manager.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::expr;

class NodeManagerWhite : public CxxTest::TestSuite {

  NodeManager* d_nm;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_nm = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() {
    delete d_scope;
    delete d_nm;
  }

  void testMkConstRational() {
    Rational i("3");
    Node n = d_nm->mkConst(i);
    Node m = d_nm->mkConst(i);
    TS_ASSERT_EQUALS(n.getId(), m.getId());
  }

  void testOversizedNodeBuilder() {
    NodeBuilder<> nb;

    TS_ASSERT_THROWS_NOTHING(nb.realloc(15));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(25));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(256));
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(nb.realloc(100), AssertionException);
#endif /* CVC4_ASSERTIONS */
    TS_ASSERT_THROWS_NOTHING(nb.realloc(257));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(4000));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(20000));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(60000));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(65535));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(65536));
    TS_ASSERT_THROWS_NOTHING(nb.realloc(67108863));
#ifdef CVC4_ASSERTIONS
    TS_ASSERT_THROWS(nb.realloc(67108863), AssertionException);
#endif /* CVC4_ASSERTIONS */
  }
};
