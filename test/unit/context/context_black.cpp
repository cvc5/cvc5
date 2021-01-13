/*********************                                                        */
/*! \file context_black.cpp
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

#include <iostream>
#include <vector>

#include "base/exception.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "test_context.h"

namespace CVC4 {

using namespace context;

namespace test {

struct MyContextNotifyObj : public ContextNotifyObj
{
  int32_t d_ncalls;

  MyContextNotifyObj(Context* context, bool pre)
      : ContextNotifyObj(context, pre), d_ncalls(0)
  {
  }

  ~MyContextNotifyObj() override {}

  void contextNotifyPop() override { ++d_ncalls; }
};

class MyContextObj : public ContextObj
{
  MyContextNotifyObj& notify;

 public:
  MyContextObj(Context* context, MyContextNotifyObj& n)
      : ContextObj(context), notify(n), d_ncalls(0), d_nsaves(0)
  {
  }

  MyContextObj(bool topScope, Context* context, MyContextNotifyObj& n)
      : ContextObj(topScope, context), notify(n), d_ncalls(0), d_nsaves(0)
  {
  }

  ~MyContextObj() override { destroy(); }

  ContextObj* save(ContextMemoryManager* pcmm) override
  {
    ++d_nsaves;
    return new (pcmm) MyContextObj(*this);
  }

  void restore(ContextObj* contextObj) override { d_ncalls = notify.d_ncalls; }

  void makeCurrent() { ContextObj::makeCurrent(); }

  int d_ncalls;
  int d_nsaves;

 private:
  MyContextObj(const MyContextObj& other)
      : ContextObj(other), notify(other.notify), d_ncalls(0), d_nsaves(0)
  {
  }
};

class TestContextBlack : public TestContext
{
};

TEST_F(TestContextBlack, push_pop)
{
  // Test what happens when the context is popped below 0
  // the interface doesn't declare any exceptions
  d_context->push();
  d_context->pop();
#ifdef CVC4_ASSERTIONS
  ASSERT_DEATH(d_context->pop(), "Cannot pop below level 0");
  ASSERT_DEATH(d_context->pop(), "Cannot pop below level 0");
#endif /* CVC4_ASSERTIONS */
}

TEST_F(TestContextBlack, dtor)
{
  // Destruction of ContextObj was broken in revision 324 (bug #45) when
  // at a higher context level with an intervening modification.
  // (The following caused a "pure virtual method called" error.)
  CDO<int> i(d_context.get());
  d_context->push();
  i = 5;
}

TEST_F(TestContextBlack, pre_post_notify)
{
  // This is tricky; we want to detect if pre- and post-notifies are
  // done correctly.  For that, we have to use a special ContextObj,
  // since that's the only thing that runs between pre- and post-.

  MyContextNotifyObj a(d_context.get(), true), b(d_context.get(), false);

  try
  {
    MyContextNotifyObj c(d_context.get(), true), d(d_context.get(), false);

    ASSERT_EQ(a.d_ncalls, 0);
    ASSERT_EQ(b.d_ncalls, 0);
    ASSERT_EQ(c.d_ncalls, 0);
    ASSERT_EQ(d.d_ncalls, 0);

    MyContextObj w(d_context.get(), a);
    MyContextObj x(d_context.get(), b);
    MyContextObj y(d_context.get(), c);
    MyContextObj z(d_context.get(), d);

    d_context->push();

    w.makeCurrent();
    x.makeCurrent();
    y.makeCurrent();
    z.makeCurrent();

    ASSERT_EQ(a.d_ncalls, 0);
    ASSERT_EQ(b.d_ncalls, 0);
    ASSERT_EQ(c.d_ncalls, 0);
    ASSERT_EQ(d.d_ncalls, 0);

    ASSERT_EQ(w.d_ncalls, 0);
    ASSERT_EQ(x.d_ncalls, 0);
    ASSERT_EQ(y.d_ncalls, 0);
    ASSERT_EQ(z.d_ncalls, 0);

    d_context->push();

    w.makeCurrent();
    x.makeCurrent();
    y.makeCurrent();
    z.makeCurrent();

    ASSERT_EQ(a.d_ncalls, 0);
    ASSERT_EQ(b.d_ncalls, 0);
    ASSERT_EQ(c.d_ncalls, 0);
    ASSERT_EQ(d.d_ncalls, 0);

    ASSERT_EQ(w.d_ncalls, 0);
    ASSERT_EQ(x.d_ncalls, 0);
    ASSERT_EQ(y.d_ncalls, 0);
    ASSERT_EQ(z.d_ncalls, 0);

    d_context->pop();

    ASSERT_EQ(a.d_ncalls, 1);
    ASSERT_EQ(b.d_ncalls, 1);
    ASSERT_EQ(c.d_ncalls, 1);
    ASSERT_EQ(d.d_ncalls, 1);

    ASSERT_EQ(w.d_ncalls, 1);
    ASSERT_EQ(x.d_ncalls, 0);
    ASSERT_EQ(y.d_ncalls, 1);
    ASSERT_EQ(z.d_ncalls, 0);

    d_context->pop();

    ASSERT_EQ(a.d_ncalls, 2);
    ASSERT_EQ(b.d_ncalls, 2);
    ASSERT_EQ(c.d_ncalls, 2);
    ASSERT_EQ(d.d_ncalls, 2);

    ASSERT_EQ(w.d_ncalls, 2);
    ASSERT_EQ(x.d_ncalls, 1);
    ASSERT_EQ(y.d_ncalls, 2);
    ASSERT_EQ(z.d_ncalls, 1);
  }
  catch (Exception& e)
  {
    std::cerr << e.toString() << std::endl;
    ASSERT_TRUE(false) << "Exception thrown from test";
  }

  // we do this (together with the { } block above) to get full code
  // coverage of destruction paths; a and b haven't been destructed
  // yet, here.
  d_context.reset(nullptr);
}

TEST_F(TestContextBlack, top_scope_context_obj)
{
  // this test's implementation is based on the fact that a
  // ContextObj allocated primordially "in the top scope" (first arg
  // to ctor is "true"), doesn't get updated if you immediately call
  // makeCurrent().

  MyContextNotifyObj n(d_context.get(), true);

  d_context->push();

  MyContextObj x(true, d_context.get(), n);
  MyContextObj y(false, d_context.get(), n);

  ASSERT_EQ(x.d_nsaves, 0);
  ASSERT_EQ(y.d_nsaves, 0);

  x.makeCurrent();
  y.makeCurrent();

  ASSERT_EQ(x.d_nsaves, 0);
  ASSERT_EQ(y.d_nsaves, 1);

  d_context->push();

  x.makeCurrent();
  y.makeCurrent();

  ASSERT_EQ(x.d_nsaves, 1);
  ASSERT_EQ(y.d_nsaves, 2);

  d_context->pop();
  d_context->pop();

  ASSERT_EQ(x.d_nsaves, 1);
  ASSERT_EQ(y.d_nsaves, 2);
}

}  // namespace test
}  // namespace CVC4
