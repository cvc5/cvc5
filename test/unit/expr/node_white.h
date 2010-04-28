/*********************                                                        */
/** node_white.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

#include <string>

#include "expr/node_value.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "context/context.h"
#include "util/Assert.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::expr;
using namespace std;

class NodeWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_ctxt = new Context();
    d_nm = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() {
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
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
    TS_ASSERT(b.d_nv->getNumChildren() == 0);
    /* etc. */
  }
};
