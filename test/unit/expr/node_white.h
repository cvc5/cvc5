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
#include "expr/attribute.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace std;

struct Test1;
struct Test2;
struct Test3;
struct Test4;

typedef Attribute<Test1, std::string> TestStringAttr1;
typedef Attribute<Test2, std::string> TestStringAttr2;

typedef Attribute<Test3, bool> TestFlag1;
typedef Attribute<Test4, bool> TestFlag2;

class NodeWhite : public CxxTest::TestSuite {

  NodeManagerScope *d_scope;
  NodeManager *d_nm;

public:

  void setUp() {
    d_nm = new NodeManager();
    d_scope = new NodeManagerScope(d_nm);
  }

  void tearDown() {
    delete d_nm;
    delete d_scope;
  }

  void testNull() {
    Node::s_null;
  }

  void testCopyCtor() {
    Node e(Node::s_null);
  }

  void testBuilder() {
    NodeBuilder<> b;
    TS_ASSERT(b.d_ev->getId() == 0);
    TS_ASSERT(b.d_ev->getKind() == UNDEFINED_KIND);
    TS_ASSERT(b.d_ev->getNumChildren() == 0);
    /* etc. */
  }

  void testAttributeIds() {
    TS_ASSERT(VarNameAttr::s_id == 0);
    TS_ASSERT(TestStringAttr1::s_id == 1);
    TS_ASSERT(TestStringAttr2::s_id == 2);
    TS_ASSERT(attr::LastAttributeId<string>::s_id == 3);

    TS_ASSERT(TypeAttr::s_id == 0);
    TS_ASSERT(attr::LastAttributeId<void*>::s_id == 1);

    TS_ASSERT(TestFlag1::s_id == 0);
    TS_ASSERT(TestFlag2::s_id == 1);
    TS_ASSERT(attr::LastAttributeId<bool>::s_id == 2);
    TS_ASSERT(TestFlag1::s_bit == 0);
    TS_ASSERT(TestFlag2::s_bit == 1);
    TS_ASSERT(attr::BitAssignment::s_bit == 2);
  }

  void testAttributes() {
    AttributeManager& am = d_nm->d_am;

    Node a = d_nm->mkVar();
    Node b = d_nm->mkVar();
    Node c = d_nm->mkVar();
    Node unnamed = d_nm->mkVar();

    a.setAttribute(VarNameAttr(), "a");
    b.setAttribute(VarNameAttr(), "b");
    c.setAttribute(VarNameAttr(), "c");

    a.setAttribute(TestFlag1(), true);
    b.setAttribute(TestFlag1(), false);
    c.setAttribute(TestFlag1(), false);
    unnamed.setAttribute(TestFlag1(), true);

    a.setAttribute(TestFlag2(), false);
    b.setAttribute(TestFlag2(), true);
    c.setAttribute(TestFlag2(), true);
    unnamed.setAttribute(TestFlag2(), false);

    TS_ASSERT(a.getAttribute(VarNameAttr()) == "a");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(b.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(b.getAttribute(VarNameAttr()) == "b");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(c.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(c.getAttribute(VarNameAttr()) == "c");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) == "");

    TS_ASSERT(! unnamed.hasAttribute(VarNameAttr()));

    TS_ASSERT(! a.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! b.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! c.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr1()));

    TS_ASSERT(! a.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! b.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! c.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr2()));

    TS_ASSERT(a.getAttribute(TestFlag1()));
    TS_ASSERT(! b.getAttribute(TestFlag1()));
    TS_ASSERT(! c.getAttribute(TestFlag1()));
    TS_ASSERT(unnamed.getAttribute(TestFlag1()));

    TS_ASSERT(! a.getAttribute(TestFlag2()));
    TS_ASSERT(b.getAttribute(TestFlag2()));
    TS_ASSERT(c.getAttribute(TestFlag2()));
    TS_ASSERT(! unnamed.getAttribute(TestFlag2()));

    a.setAttribute(TestStringAttr1(), "foo");
    b.setAttribute(TestStringAttr1(), "bar");
    c.setAttribute(TestStringAttr1(), "baz");

    TS_ASSERT(a.getAttribute(VarNameAttr()) == "a");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(b.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(b.getAttribute(VarNameAttr()) == "b");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(c.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(c.getAttribute(VarNameAttr()) == "c");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) == "");

    TS_ASSERT(! unnamed.hasAttribute(VarNameAttr()));

    TS_ASSERT(a.hasAttribute(TestStringAttr1()));
    TS_ASSERT(b.hasAttribute(TestStringAttr1()));
    TS_ASSERT(c.hasAttribute(TestStringAttr1()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr1()));

    TS_ASSERT(! a.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! b.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! c.hasAttribute(TestStringAttr2()));
    TS_ASSERT(! unnamed.hasAttribute(TestStringAttr2()));

    a.setAttribute(VarNameAttr(), "b");
    b.setAttribute(VarNameAttr(), "c");
    c.setAttribute(VarNameAttr(), "a");

    TS_ASSERT(c.getAttribute(VarNameAttr()) == "a");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(c.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(a.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(a.getAttribute(VarNameAttr()) == "b");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(a.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(b.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(b.getAttribute(VarNameAttr()) == "c");
    TS_ASSERT(b.getAttribute(VarNameAttr()) != "");

    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "a");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "b");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) != "c");
    TS_ASSERT(unnamed.getAttribute(VarNameAttr()) == "");

    TS_ASSERT(! unnamed.hasAttribute(VarNameAttr()));

  }
};
