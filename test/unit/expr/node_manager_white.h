/*********************                                                        */
/*! \file node_manager_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::NodeManager.
 **
 ** White box testing of CVC4::NodeManager.
 **/

#include <cxxtest/TestSuite.h>

#include <string>

#include "expr/node_manager.h"
#include "context/context.h"

#include "util/rational.h"
#include "util/integer.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::context;

class NodeManagerWhite : public CxxTest::TestSuite {

  Context* d_ctxt;
  NodeManager* d_nm;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_ctxt = new Context();
    d_nm = new NodeManager(d_ctxt, NULL);
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() {
    delete d_scope;
    delete d_nm;
    delete d_ctxt;
  }

  void testMkConstInt() {
    Integer i("3");
    Node n = d_nm->mkConst(i);
    Node m = d_nm->mkConst(i);
    TS_ASSERT_EQUALS(n.getId(), m.getId());
  }
};
