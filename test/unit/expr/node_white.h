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
struct Test5;

typedef Attribute<Test1, std::string> TestStringAttr1;
typedef Attribute<Test2, std::string> TestStringAttr2;

typedef Attribute<Test1, bool> TestFlag1;
typedef Attribute<Test2, bool> TestFlag2;
typedef Attribute<Test3, bool> TestFlag3;
typedef Attribute<Test4, bool> TestFlag4;
typedef Attribute<Test5, bool> TestFlag5;

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
    TS_ASSERT(b.d_nv->getId() == 0);
    TS_ASSERT(b.d_nv->getKind() == UNDEFINED_KIND);
    TS_ASSERT(b.d_nv->getNumChildren() == 0);
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
    TS_ASSERT(TestFlag3::s_id == 2);
    TS_ASSERT(TestFlag4::s_id == 3);
    TS_ASSERT(TestFlag5::s_id == 4);
    TS_ASSERT(attr::LastAttributeId<bool>::s_id == 5);
  }

  void testAttributes() {
    AttributeManager& am = d_nm->d_attrManager;

    //Debug.on("boolattr");

    Node a = d_nm->mkVar();
    Node b = d_nm->mkVar();
    Node c = d_nm->mkVar();
    Node unnamed = d_nm->mkVar();

    a.setAttribute(VarNameAttr(), "a");
    b.setAttribute(VarNameAttr(), "b");
    c.setAttribute(VarNameAttr(), "c");

    // test that all boolean flags are FALSE to start
    Debug("boolattr", "get flag 1 on a (should be F)\n");
    TS_ASSERT(! a.getAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on b (should be F)\n");
    TS_ASSERT(! b.getAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on unnamed (should be F)\n");
    TS_ASSERT(! unnamed.getAttribute(TestFlag1()));

    Debug("boolattr", "get flag 2 on a (should be F)\n");
    TS_ASSERT(! a.getAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on b (should be F)\n");
    TS_ASSERT(! b.getAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on unnamed (should be F)\n");
    TS_ASSERT(! unnamed.getAttribute(TestFlag2()));

    Debug("boolattr", "get flag 3 on a (should be F)\n");
    TS_ASSERT(! a.getAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on b (should be F)\n");
    TS_ASSERT(! b.getAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on unnamed (should be F)\n");
    TS_ASSERT(! unnamed.getAttribute(TestFlag3()));

    Debug("boolattr", "get flag 4 on a (should be F)\n");
    TS_ASSERT(! a.getAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on b (should be F)\n");
    TS_ASSERT(! b.getAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on unnamed (should be F)\n");
    TS_ASSERT(! unnamed.getAttribute(TestFlag4()));

    Debug("boolattr", "get flag 5 on a (should be F)\n");
    TS_ASSERT(! a.getAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on b (should be F)\n");
    TS_ASSERT(! b.getAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on unnamed (should be F)\n");
    TS_ASSERT(! unnamed.getAttribute(TestFlag5()));

    // test that they all HAVE the boolean attributes
    Debug("boolattr", "get flag 1 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag1()));

    Debug("boolattr", "get flag 2 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag2()));

    Debug("boolattr", "get flag 3 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag3()));

    Debug("boolattr", "get flag 4 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag4()));

    Debug("boolattr", "get flag 5 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag5()));

    // test two-arg version of hasAttribute()
    bool bb;
    Debug("boolattr", "get flag 1 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag1(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 1 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag1(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 1 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag1(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 1 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag1(), &bb));
    TS_ASSERT(! bb);

    Debug("boolattr", "get flag 2 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag2(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 2 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag2(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 2 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag2(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 2 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag2(), &bb));
    TS_ASSERT(! bb);

    Debug("boolattr", "get flag 3 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag3(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 3 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag3(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 3 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag3(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 3 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag3(), &bb));
    TS_ASSERT(! bb);

    Debug("boolattr", "get flag 4 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag4(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 4 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag4(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 4 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag4(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 4 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag4(), &bb));
    TS_ASSERT(! bb);

    Debug("boolattr", "get flag 5 on a (should be F)\n");
    TS_ASSERT(a.hasAttribute(TestFlag5(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 5 on b (should be F)\n");
    TS_ASSERT(b.hasAttribute(TestFlag5(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 5 on c (should be F)\n");
    TS_ASSERT(c.hasAttribute(TestFlag5(), &bb));
    TS_ASSERT(! bb);
    Debug("boolattr", "get flag 5 on unnamed (should be F)\n");
    TS_ASSERT(unnamed.hasAttribute(TestFlag5(), &bb));
    TS_ASSERT(! bb);

    // setting boolean flags
    Debug("boolattr", "set flag 1 on a to T\n");
    a.setAttribute(TestFlag1(), true);
    Debug("boolattr", "set flag 1 on b to F\n");
    b.setAttribute(TestFlag1(), false);
    Debug("boolattr", "set flag 1 on c to F\n");
    c.setAttribute(TestFlag1(), false);
    Debug("boolattr", "set flag 1 on unnamed to T\n");
    unnamed.setAttribute(TestFlag1(), true);

    Debug("boolattr", "set flag 2 on a to F\n");
    a.setAttribute(TestFlag2(), false);
    Debug("boolattr", "set flag 2 on b to T\n");
    b.setAttribute(TestFlag2(), true);
    Debug("boolattr", "set flag 2 on c to T\n");
    c.setAttribute(TestFlag2(), true);
    Debug("boolattr", "set flag 2 on unnamed to F\n");
    unnamed.setAttribute(TestFlag2(), false);

    Debug("boolattr", "set flag 3 on a to T\n");
    a.setAttribute(TestFlag3(), true);
    Debug("boolattr", "set flag 3 on b to T\n");
    b.setAttribute(TestFlag3(), true);
    Debug("boolattr", "set flag 3 on c to T\n");
    c.setAttribute(TestFlag3(), true);
    Debug("boolattr", "set flag 3 on unnamed to T\n");
    unnamed.setAttribute(TestFlag3(), true);

    Debug("boolattr", "set flag 4 on a to T\n");
    a.setAttribute(TestFlag4(), true);
    Debug("boolattr", "set flag 4 on b to T\n");
    b.setAttribute(TestFlag4(), true);
    Debug("boolattr", "set flag 4 on c to T\n");
    c.setAttribute(TestFlag4(), true);
    Debug("boolattr", "set flag 4 on unnamed to T\n");
    unnamed.setAttribute(TestFlag4(), true);

    Debug("boolattr", "set flag 5 on a to T\n");
    a.setAttribute(TestFlag5(), true);
    Debug("boolattr", "set flag 5 on b to T\n");
    b.setAttribute(TestFlag5(), true);
    Debug("boolattr", "set flag 5 on c to F\n");
    c.setAttribute(TestFlag5(), false);
    Debug("boolattr", "set flag 5 on unnamed to T\n");
    unnamed.setAttribute(TestFlag5(), true);

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

    Debug("boolattr", "get flag 1 on a (should be T)\n");
    TS_ASSERT(a.getAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on b (should be F)\n");
    TS_ASSERT(! b.getAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag1()));
    Debug("boolattr", "get flag 1 on unnamed (should be T)\n");
    TS_ASSERT(unnamed.getAttribute(TestFlag1()));

    Debug("boolattr", "get flag 2 on a (should be F)\n");
    TS_ASSERT(! a.getAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on b (should be T)\n");
    TS_ASSERT(b.getAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on c (should be T)\n");
    TS_ASSERT(c.getAttribute(TestFlag2()));
    Debug("boolattr", "get flag 2 on unnamed (should be F)\n");
    TS_ASSERT(! unnamed.getAttribute(TestFlag2()));

    Debug("boolattr", "get flag 3 on a (should be T)\n");
    TS_ASSERT(a.getAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on b (should be T)\n");
    TS_ASSERT(b.getAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on c (should be T)\n");
    TS_ASSERT(c.getAttribute(TestFlag3()));
    Debug("boolattr", "get flag 3 on unnamed (should be T)\n");
    TS_ASSERT(unnamed.getAttribute(TestFlag3()));

    Debug("boolattr", "get flag 4 on a (should be T)\n");
    TS_ASSERT(a.getAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on b (should be T)\n");
    TS_ASSERT(b.getAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on c (should be T)\n");
    TS_ASSERT(c.getAttribute(TestFlag4()));
    Debug("boolattr", "get flag 4 on unnamed (should be T)\n");
    TS_ASSERT(unnamed.getAttribute(TestFlag4()));

    Debug("boolattr", "get flag 5 on a (should be T)\n");
    TS_ASSERT(a.getAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on b (should be T)\n");
    TS_ASSERT(b.getAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on c (should be F)\n");
    TS_ASSERT(! c.getAttribute(TestFlag5()));
    Debug("boolattr", "get flag 5 on unnamed (should be T)\n");
    TS_ASSERT(unnamed.getAttribute(TestFlag5()));

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
