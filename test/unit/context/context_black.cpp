/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::context::Context.
 */

#include <iostream>
#include <vector>

#include "base/exception.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "test_context.h"

namespace cvc5::internal {

using namespace context;

namespace test {

struct MyContextNotifyObj : public ContextNotifyObj
{
  MyContextNotifyObj(Context* context, bool pre)
      : ContextNotifyObj(context, pre), d_ncalls(0)
  {
  }

  ~MyContextNotifyObj() override {}

  void contextNotifyPop() override { ++d_ncalls; }

  int32_t d_ncalls;
};

class MyContextObj : public ContextObj
{
 public:
  MyContextObj(Context* context, MyContextNotifyObj& n)
      : ContextObj(context), d_ncalls(0), d_nsaves(0), d_notify(n)
  {
  }

  ~MyContextObj() override { destroy(); }

  ContextObj* save(ContextMemoryManager* pcmm) override
  {
    ++d_nsaves;
    return new (pcmm) MyContextObj(*this);
  }

  void restore(ContextObj* contextObj) override
  {
    d_ncalls = d_notify.d_ncalls;
  }

  void makeCurrent() { ContextObj::makeCurrent(); }

  int32_t d_ncalls;
  int32_t d_nsaves;

 private:
  MyContextObj(const MyContextObj& other)
      : ContextObj(other), d_ncalls(0), d_nsaves(0), d_notify(other.d_notify)
  {
  }
  MyContextNotifyObj& d_notify;
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
#ifdef CVC5_ASSERTIONS
  ASSERT_DEATH(d_context->pop(), "Cannot pop below level 0");
  ASSERT_DEATH(d_context->pop(), "Cannot pop below level 0");
#endif /* CVC5_ASSERTIONS */
}

TEST_F(TestContextBlack, dtor)
{
  // Destruction of ContextObj was broken in revision 324 (bug #45) when
  // at a higher context level with an intervening modification.
  // (The following caused a "pure virtual method called" error.)
  CDO<int32_t> i(d_context.get());
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

TEST_F(TestContextBlack, detect_invalid_obj)
{
  MyContextNotifyObj n(d_context.get(), true);

  {
    // Objects allocated at the bottom scope are allowed to outlive the scope
    // that they have been allocated in.
    d_context->push();
    MyContextObj x(d_context.get(), n);
    d_context->pop();
  }
}

}  // namespace test
}  // namespace cvc5::internal
