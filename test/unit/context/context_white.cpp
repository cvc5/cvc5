/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::context::Context.
 */

#include "base/check.h"
#include "context/cdo.h"
#include "test_context.h"

namespace cvc5::internal {

using namespace context;

namespace test {

class TestContextWhite : public TestContext
{
};

TEST_F(TestContextWhite, simple)
{
  Scope* s = d_context->getTopScope();

  ASSERT_EQ(s, d_context->getBottomScope());
  ASSERT_EQ(d_context->getLevel(), 0);
  ASSERT_EQ(d_context->d_scopeList.size(), 1);

  ASSERT_EQ(s->d_pContext, d_context.get());
  ASSERT_EQ(s->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(s->d_level, 0);
  ASSERT_EQ(s->d_pContextObjList, nullptr);

  CDO<int> a(d_context.get());

  ASSERT_EQ(s->d_pContext, d_context.get());
  ASSERT_EQ(s->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(s->d_level, 0);
  ASSERT_EQ(s->d_pContextObjList, &a);

  ASSERT_EQ(a.d_pScope, s);
  ASSERT_EQ(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &s->d_pContextObjList);

  CDO<int> b(d_context.get());

  ASSERT_EQ(s->d_pContext, d_context.get());
  ASSERT_EQ(s->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(s->d_level, 0);
  ASSERT_EQ(s->d_pContextObjList, &b);

  ASSERT_EQ(a.d_pScope, s);
  ASSERT_EQ(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  ASSERT_EQ(b.d_pScope, s);
  ASSERT_EQ(b.d_pContextObjRestore, nullptr);
  ASSERT_EQ(b.d_pContextObjNext, &a);
  ASSERT_EQ(b.d_ppContextObjPrev, &s->d_pContextObjList);

  d_context->push();
  Scope* t = d_context->getTopScope();
  ASSERT_NE(s, t);

  ASSERT_EQ(s, d_context->getBottomScope());
  ASSERT_EQ(d_context->getLevel(), 1);
  ASSERT_EQ(d_context->d_scopeList.size(), 2);

  ASSERT_EQ(s->d_pContext, d_context.get());
  ASSERT_EQ(s->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(s->d_level, 0);
  ASSERT_EQ(s->d_pContextObjList, &b);

  ASSERT_EQ(t->d_pContext, d_context.get());
  ASSERT_EQ(t->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(t->d_level, 1);
  ASSERT_EQ(t->d_pContextObjList, nullptr);

  ASSERT_EQ(a.d_pScope, s);
  ASSERT_EQ(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  ASSERT_EQ(b.d_pScope, s);
  ASSERT_EQ(b.d_pContextObjRestore, nullptr);
  ASSERT_EQ(b.d_pContextObjNext, &a);
  ASSERT_EQ(b.d_ppContextObjPrev, &s->d_pContextObjList);

  a = 5;

  ASSERT_EQ(t->d_pContext, d_context.get());
  ASSERT_EQ(t->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(t->d_level, 1);
  ASSERT_EQ(t->d_pContextObjList, &a);

  ASSERT_EQ(a.d_pScope, t);
  ASSERT_NE(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &t->d_pContextObjList);

  b = 3;

  ASSERT_EQ(t->d_pContext, d_context.get());
  ASSERT_EQ(t->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(t->d_level, 1);
  ASSERT_EQ(t->d_pContextObjList, &b);

  ASSERT_EQ(a.d_pScope, t);
  ASSERT_NE(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  ASSERT_EQ(b.d_pScope, t);
  ASSERT_NE(b.d_pContextObjRestore, nullptr);
  ASSERT_EQ(b.d_pContextObjNext, &a);
  ASSERT_EQ(b.d_ppContextObjPrev, &t->d_pContextObjList);

  d_context->push();
  Scope* u = d_context->getTopScope();
  ASSERT_NE(u, t);
  ASSERT_NE(u, s);

  CDO<int> c(d_context.get());
  c = 4;

  ASSERT_EQ(c.d_pScope, u);
  ASSERT_NE(c.d_pContextObjRestore, nullptr);
  ASSERT_EQ(c.d_pContextObjNext, nullptr);
  ASSERT_EQ(c.d_ppContextObjPrev, &u->d_pContextObjList);

  d_context->pop();

  ASSERT_EQ(t->d_pContext, d_context.get());
  ASSERT_EQ(t->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(t->d_level, 1);
  ASSERT_EQ(t->d_pContextObjList, &b);

  ASSERT_EQ(a.d_pScope, t);
  ASSERT_NE(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  ASSERT_EQ(b.d_pScope, t);
  ASSERT_NE(b.d_pContextObjRestore, nullptr);
  ASSERT_EQ(b.d_pContextObjNext, &a);
  ASSERT_EQ(b.d_ppContextObjPrev, &t->d_pContextObjList);

  d_context->pop();

  ASSERT_EQ(s->d_pContext, d_context.get());
  ASSERT_EQ(s->d_pCMM, d_context->d_pCMM);
  ASSERT_EQ(s->d_level, 0);
  ASSERT_EQ(s->d_pContextObjList, &c);

  ASSERT_EQ(a.d_pScope, s);
  ASSERT_EQ(a.d_pContextObjRestore, nullptr);
  ASSERT_EQ(a.d_pContextObjNext, nullptr);
  ASSERT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  ASSERT_EQ(b.d_pScope, s);
  ASSERT_EQ(b.d_pContextObjRestore, nullptr);
  ASSERT_EQ(b.d_pContextObjNext, &a);
  ASSERT_EQ(b.d_ppContextObjPrev, &c.d_pContextObjNext);

  ASSERT_EQ(c.d_pScope, s);
  ASSERT_EQ(c.d_pContextObjRestore, nullptr);
  ASSERT_EQ(c.d_pContextObjNext, &b);
  ASSERT_EQ(c.d_ppContextObjPrev, &s->d_pContextObjList);
}
}  // namespace test
}  // namespace cvc5::internal
