/*********************                                                        */
/*! \file context_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::Context.
 **
 ** Black box testing of CVC4::context::Context.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <vector>

#include "base/exception.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/context.h"
#include "test_utils.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

struct MyContextNotifyObj : public ContextNotifyObj {
  int nCalls;

  MyContextNotifyObj(Context* context, bool pre) :
    ContextNotifyObj(context, pre),
    nCalls(0) {
  }

  ~MyContextNotifyObj() override {}

  void contextNotifyPop() override { ++nCalls; }
};

class MyContextObj : public ContextObj {
  MyContextNotifyObj& notify;

public:
  int nCalls;
  int nSaves;

private:
  MyContextObj(const MyContextObj& other) :
    ContextObj(other),
    notify(other.notify),
    nCalls(0),
    nSaves(0) {
  }

public:

  MyContextObj(Context* context, MyContextNotifyObj& n) :
    ContextObj(context),
    notify(n),
    nCalls(0),
    nSaves(0) {
  }

  MyContextObj(bool topScope, Context* context, MyContextNotifyObj& n) :
    ContextObj(topScope, context),
    notify(n),
    nCalls(0),
    nSaves(0) {
  }

  ~MyContextObj() override { destroy(); }

  ContextObj* save(ContextMemoryManager* pcmm) override
  {
    ++nSaves;
    return new(pcmm) MyContextObj(*this);
  }

  void restore(ContextObj* contextObj) override { nCalls = notify.nCalls; }

  void makeCurrent() {
    ContextObj::makeCurrent();
  }
};


class ContextBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

 public:
  void setUp() override { d_context = new Context; }

  void tearDown() override { delete d_context; }

  void testContextPushPop()
  {
    // Test what happens when the context is popped below 0
    // the interface doesn't declare any exceptions
    d_context->push();
    d_context->pop();
#ifdef CVC4_ASSERTIONS
    TS_UTILS_EXPECT_ABORT(d_context->pop());
    TS_UTILS_EXPECT_ABORT(d_context->pop());
#endif /* CVC4_ASSERTIONS */
  }

  void testDtor() {
    // Destruction of ContextObj was broken in revision 324 (bug #45) when
    // at a higher context level with an intervening modification.
    // (The following caused a "pure virtual method called" error.)
    CDO<int> i(d_context);
    d_context->push();
    i = 5;
  }

  void testPrePostNotify() {
    // This is tricky; we want to detect if pre- and post-notifies are
    // done correctly.  For that, we have to use a special ContextObj,
    // since that's the only thing that runs between pre- and post-.

    MyContextNotifyObj a(d_context, true), b(d_context, false);

    try {
      MyContextNotifyObj c(d_context, true), d(d_context, false);

      TS_ASSERT_EQUALS(a.nCalls, 0);
      TS_ASSERT_EQUALS(b.nCalls, 0);
      TS_ASSERT_EQUALS(c.nCalls, 0);
      TS_ASSERT_EQUALS(d.nCalls, 0);

      MyContextObj w(d_context, a);
      MyContextObj x(d_context, b);
      MyContextObj y(d_context, c);
      MyContextObj z(d_context, d);

      d_context->push();

      w.makeCurrent();
      x.makeCurrent();
      y.makeCurrent();
      z.makeCurrent();

      TS_ASSERT_EQUALS(a.nCalls, 0);
      TS_ASSERT_EQUALS(b.nCalls, 0);
      TS_ASSERT_EQUALS(c.nCalls, 0);
      TS_ASSERT_EQUALS(d.nCalls, 0);

      TS_ASSERT_EQUALS(w.nCalls, 0);
      TS_ASSERT_EQUALS(x.nCalls, 0);
      TS_ASSERT_EQUALS(y.nCalls, 0);
      TS_ASSERT_EQUALS(z.nCalls, 0);

      d_context->push();

      w.makeCurrent();
      x.makeCurrent();
      y.makeCurrent();
      z.makeCurrent();

      TS_ASSERT_EQUALS(a.nCalls, 0);
      TS_ASSERT_EQUALS(b.nCalls, 0);
      TS_ASSERT_EQUALS(c.nCalls, 0);
      TS_ASSERT_EQUALS(d.nCalls, 0);

      TS_ASSERT_EQUALS(w.nCalls, 0);
      TS_ASSERT_EQUALS(x.nCalls, 0);
      TS_ASSERT_EQUALS(y.nCalls, 0);
      TS_ASSERT_EQUALS(z.nCalls, 0);

      d_context->pop();

      TS_ASSERT_EQUALS(a.nCalls, 1);
      TS_ASSERT_EQUALS(b.nCalls, 1);
      TS_ASSERT_EQUALS(c.nCalls, 1);
      TS_ASSERT_EQUALS(d.nCalls, 1);

      TS_ASSERT_EQUALS(w.nCalls, 1);
      TS_ASSERT_EQUALS(x.nCalls, 0);
      TS_ASSERT_EQUALS(y.nCalls, 1);
      TS_ASSERT_EQUALS(z.nCalls, 0);

      d_context->pop();

      TS_ASSERT_EQUALS(a.nCalls, 2);
      TS_ASSERT_EQUALS(b.nCalls, 2);
      TS_ASSERT_EQUALS(c.nCalls, 2);
      TS_ASSERT_EQUALS(d.nCalls, 2);

      TS_ASSERT_EQUALS(w.nCalls, 2);
      TS_ASSERT_EQUALS(x.nCalls, 1);
      TS_ASSERT_EQUALS(y.nCalls, 2);
      TS_ASSERT_EQUALS(z.nCalls, 1);
    } catch(Exception& e) {
      cerr << e.toString() << endl;
      TS_FAIL("Exception thrown from test");
    }

    // we do this (together with the { } block above) to get full code
    // coverage of destruction paths; a and b haven't been destructed
    // yet, here.
    delete d_context;

    d_context = NULL;
  }

  void testTopScopeContextObj() {
    // this test's implementation is based on the fact that a
    // ContextObj allocated primordially "in the top scope" (first arg
    // to ctor is "true"), doesn't get updated if you immediately call
    // makeCurrent().

    MyContextNotifyObj n(d_context, true);

    d_context->push();

    MyContextObj x(true, d_context, n);
    MyContextObj y(false, d_context, n);

    TS_ASSERT_EQUALS(x.nSaves, 0);
    TS_ASSERT_EQUALS(y.nSaves, 0);

    x.makeCurrent();
    y.makeCurrent();

    TS_ASSERT_EQUALS(x.nSaves, 0);
    TS_ASSERT_EQUALS(y.nSaves, 1);

    d_context->push();

    x.makeCurrent();
    y.makeCurrent();

    TS_ASSERT_EQUALS(x.nSaves, 1);
    TS_ASSERT_EQUALS(y.nSaves, 2);

    d_context->pop();
    d_context->pop();

    TS_ASSERT_EQUALS(x.nSaves, 1);
    TS_ASSERT_EQUALS(y.nSaves, 2);
  }
};
