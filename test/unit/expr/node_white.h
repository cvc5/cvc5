/*********************                                           -*- C++ -*-  */
/** node_white.h
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
 ** White box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

#include "expr/node.h"

using namespace CVC4;

class NodeWhite : public CxxTest::TestSuite {
public:

  void testNull() {
    Node::s_null;
  }

  void testCopyCtor() {
    Node e(Node::s_null);
  }
};
