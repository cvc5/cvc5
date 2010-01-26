/*********************                                           -*- C++ -*-  */
/** node_black.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

#include "expr/node_manager.h"
#include "expr/node.h"

using namespace CVC4;
using namespace std;

class NodeBlack : public CxxTest::TestSuite {
private:

  NodeManagerScope *d_scope;
  NodeManager *d_nm;

public:

  void setUp() {
    d_nm = new NodeManager();
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown(){
    delete d_nm;
    delete d_scope;
  }

  void testEqExpr(){
    /*Node eqExpr(const Node& right) const;*/
    Node left = d_nm->mkNode(TRUE);
    Node right = d_nm->mkNode(NOT,(d_nm->mkNode(FALSE)));

    Node eq = left.eqExpr(right);

    Node first = *(eq.begin());
    Node second = *(eq.begin()++);

    TS_ASSERT(first.getKind() == NULL);
    TS_ASSERT(second.getKind() == NULL);
  }

};
