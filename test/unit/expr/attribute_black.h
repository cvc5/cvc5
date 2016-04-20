/*********************                                                        */
/*! \file attribute_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Attribute.
 **
 ** Black box testing of CVC4::Attribute.
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
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::smt;
using namespace std;

class AttributeBlack : public CxxTest::TestSuite {
private:

  ExprManager* d_exprManager;
  NodeManager* d_nodeManager;
  SmtEngine* d_smtEngine;
  SmtScope* d_scope;

public:

  void setUp() {
    d_exprManager = new ExprManager();
    d_nodeManager = NodeManager::fromExprManager(d_exprManager);
    d_smtEngine = new SmtEngine(d_exprManager);
    d_scope = new SmtScope(d_smtEngine);
  }

  void tearDown() {
    delete d_scope;
    delete d_smtEngine;
    delete d_exprManager;
  }

  class MyData {
  public:
    static int count;
    MyData()  { count ++; }
    ~MyData() { count --; }
  };

  struct MyDataAttributeId {};

  struct MyDataCleanupFunction {
    static void cleanup(MyData* myData){
      delete myData;
    }
  };

  typedef expr::Attribute<MyDataAttributeId, MyData*, MyDataCleanupFunction> MyDataAttribute;

  void testDeallocation() {
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));
    MyData* data;
    MyData* data1;
    MyDataAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data));
    node->setAttribute(attr, new MyData());
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT(MyData::count == 1);
    delete node;
  }

  struct PrimitiveIntAttributeId {};
  struct CDPrimitiveIntAttributeId {};

  typedef expr::Attribute<PrimitiveIntAttributeId,uint64_t> PrimitiveIntAttribute;
  typedef expr::CDAttribute<CDPrimitiveIntAttributeId,uint64_t> CDPrimitiveIntAttribute;
  void testInts(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));
    const uint64_t val = 63489;
    uint64_t data0 = 0;
    uint64_t data1 = 0;

    PrimitiveIntAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    uint64_t data2 = 0;
    uint64_t data3 = 0;
    CDPrimitiveIntAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

  struct TNodeAttributeId {};
  struct CDTNodeAttributeId {};

  typedef expr::Attribute<TNodeAttributeId, TNode> TNodeAttribute;
  typedef expr::CDAttribute<CDTNodeAttributeId, TNode> CDTNodeAttribute;
  void testTNodes(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

    Node val(d_nodeManager->mkSkolem("b", booleanType));
    TNode data0;
    TNode data1;

    TNodeAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    TNode data2;
    TNode data3;
    CDTNodeAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

  class Foo {
    int d_bar;
  public:
    Foo(int b) : d_bar(b) {}
    int getBar() const { return d_bar; }
  };

  struct PtrAttributeId {};
  struct CDPtrAttributeId {};

  typedef expr::Attribute<PtrAttributeId, Foo*> PtrAttribute;
  typedef expr::CDAttribute<CDPtrAttributeId, Foo*> CDPtrAttribute;
  void testPtrs(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

    Foo* val = new Foo(63489);
    Foo* data0 = NULL;
    Foo* data1 = NULL;

    PtrAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    Foo* data2 = NULL;
    Foo* data3 = NULL;
    CDPtrAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT(data3 != NULL);
    TS_ASSERT_EQUALS(63489, data3->getBar());
    TS_ASSERT_EQUALS(data3, val);
    delete node;
    delete val;
  }


  struct ConstPtrAttributeId {};
  struct CDConstPtrAttributeId {};

  typedef expr::Attribute<ConstPtrAttributeId, const Foo*> ConstPtrAttribute;
  typedef expr::CDAttribute<CDConstPtrAttributeId, const Foo*> CDConstPtrAttribute;
  void testConstPtrs(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

    const Foo* val = new Foo(63489);
    const Foo* data0 = NULL;
    const Foo* data1 = NULL;

    ConstPtrAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    const Foo* data2 = NULL;
    const Foo* data3 = NULL;
    CDConstPtrAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
    delete val;
  }

  struct StringAttributeId {};
  struct CDStringAttributeId {};

  typedef expr::Attribute<StringAttributeId, std::string> StringAttribute;
  typedef expr::CDAttribute<CDStringAttributeId, std::string> CDStringAttribute;
  void testStrings(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

    std::string val("63489");
    std::string data0;
    std::string data1;

    StringAttribute attr;
    TS_ASSERT(!node->getAttribute(attr, data0));
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    std::string data2;
    std::string data3;
    CDStringAttribute cdattr;
    TS_ASSERT(!node->getAttribute(cdattr, data2));
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

  struct BoolAttributeId {};
  struct CDBoolAttributeId {};

  typedef expr::Attribute<BoolAttributeId, bool> BoolAttribute;
  typedef expr::CDAttribute<CDBoolAttributeId, bool> CDBoolAttribute;
  void testBools(){
    TypeNode booleanType = d_nodeManager->booleanType();
    Node* node = new Node(d_nodeManager->mkSkolem("b", booleanType));

    bool val = true;
    bool data0 = false;
    bool data1 = false;

    BoolAttribute attr;
    TS_ASSERT(node->getAttribute(attr, data0));
    TS_ASSERT_EQUALS(false, data0);
    node->setAttribute(attr, val);
    TS_ASSERT(node->getAttribute(attr, data1));
    TS_ASSERT_EQUALS(data1, val);

    bool data2 = false;
    bool data3 = false;
    CDBoolAttribute cdattr;
    TS_ASSERT(node->getAttribute(cdattr, data2));
    TS_ASSERT_EQUALS(false, data2);
    node->setAttribute(cdattr, val);
    TS_ASSERT(node->getAttribute(cdattr, data3));
    TS_ASSERT_EQUALS(data3, val);
    delete node;
  }

};

int AttributeBlack::MyData::count = 0;
