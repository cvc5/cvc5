/*********************                                                        */
/** node_black.h
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>

//Used in some of the tests
#include <vector>
#include <sstream>

#include "expr/expr_manager.h"
#include "expr/node_value.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node.h"
#include "expr/attribute.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;

class AttributeBlack : public CxxTest::TestSuite {
private:

  Context* d_ctxt;
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;

public:

  void setUp() {
    d_ctxt = new Context;
    d_nodeManager = new NodeManager(d_ctxt);
    d_scope = new NodeManagerScope(d_nodeManager);
  }

  void tearDown() {
    delete d_scope;
    delete d_nodeManager;
    delete d_ctxt;
  }

  class MyData {
  public:
    static int count;
    MyData()  { count ++; }
    ~MyData() { count --; }
  };

  struct MyDataAttributeId {};

  struct MyDataCleanupFunction {
    static void cleanup(MyData*& myData){
      delete myData;
    }
  };

  typedef expr::Attribute<MyDataAttributeId, MyData*, MyDataCleanupFunction> MyDataAttribute;

  void testDeallocation() {
    Node* node = new Node(d_nodeManager->mkVar());
    MyData* data;
    MyData* data1;
    MyDataAttribute attr;
    TS_ASSERT(!node->hasAttribute(attr, data));
    node->setAttribute(attr, new MyData());
    TS_ASSERT(node->hasAttribute(attr, data1));
    TS_ASSERT(MyData::count == 1);
    delete node;
  }

};

int AttributeBlack::MyData::count = 0;
