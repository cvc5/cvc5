/*********************                                                        */
/*! \file context_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::context::Context.
 **
 ** White box testing of CVC4::context::Context.
 **/

#include "base/check.h"
#include "context/cdo.h"
#include "test_context.h"

namespace CVC4 {

using namespace context;

namespace test {

class TestContextWhite : public TestContext
{
};

TEST_F(TestContextWhite, simple)
{
  Scope* s = d_context->getTopScope();

  EXPECT_EQ(s, d_context->getBottomScope());
  EXPECT_EQ(d_context->getLevel(), 0);
  EXPECT_EQ(d_context->d_scopeList.size(), 1);

  EXPECT_EQ(s->d_pContext, d_context.get());
  EXPECT_EQ(s->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(s->d_level, 0);
  EXPECT_EQ(s->d_pContextObjList, nullptr);

  CDO<int> a(d_context.get());

  EXPECT_EQ(s->d_pContext, d_context.get());
  EXPECT_EQ(s->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(s->d_level, 0);
  EXPECT_EQ(s->d_pContextObjList, &a);

  EXPECT_EQ(a.d_pScope, s);
  EXPECT_EQ(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &s->d_pContextObjList);

  CDO<int> b(d_context.get());

  EXPECT_EQ(s->d_pContext, d_context.get());
  EXPECT_EQ(s->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(s->d_level, 0);
  EXPECT_EQ(s->d_pContextObjList, &b);

  EXPECT_EQ(a.d_pScope, s);
  EXPECT_EQ(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  EXPECT_EQ(b.d_pScope, s);
  EXPECT_EQ(b.d_pContextObjRestore, nullptr);
  EXPECT_EQ(b.d_pContextObjNext, &a);
  EXPECT_EQ(b.d_ppContextObjPrev, &s->d_pContextObjList);

  d_context->push();
  Scope* t = d_context->getTopScope();
  EXPECT_NE(s, t);

  EXPECT_EQ(s, d_context->getBottomScope());
  EXPECT_EQ(d_context->getLevel(), 1);
  EXPECT_EQ(d_context->d_scopeList.size(), 2);

  EXPECT_EQ(s->d_pContext, d_context.get());
  EXPECT_EQ(s->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(s->d_level, 0);
  EXPECT_EQ(s->d_pContextObjList, &b);

  EXPECT_EQ(t->d_pContext, d_context.get());
  EXPECT_EQ(t->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(t->d_level, 1);
  EXPECT_EQ(t->d_pContextObjList, nullptr);

  EXPECT_EQ(a.d_pScope, s);
  EXPECT_EQ(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  EXPECT_EQ(b.d_pScope, s);
  EXPECT_EQ(b.d_pContextObjRestore, nullptr);
  EXPECT_EQ(b.d_pContextObjNext, &a);
  EXPECT_EQ(b.d_ppContextObjPrev, &s->d_pContextObjList);

  a = 5;

  EXPECT_EQ(t->d_pContext, d_context.get());
  EXPECT_EQ(t->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(t->d_level, 1);
  EXPECT_EQ(t->d_pContextObjList, &a);

  EXPECT_EQ(a.d_pScope, t);
  EXPECT_NE(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &t->d_pContextObjList);

  b = 3;

  EXPECT_EQ(t->d_pContext, d_context.get());
  EXPECT_EQ(t->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(t->d_level, 1);
  EXPECT_EQ(t->d_pContextObjList, &b);

  EXPECT_EQ(a.d_pScope, t);
  EXPECT_NE(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  EXPECT_EQ(b.d_pScope, t);
  EXPECT_NE(b.d_pContextObjRestore, nullptr);
  EXPECT_EQ(b.d_pContextObjNext, &a);
  EXPECT_EQ(b.d_ppContextObjPrev, &t->d_pContextObjList);

  d_context->push();
  Scope* u = d_context->getTopScope();
  EXPECT_NE(u, t);
  EXPECT_NE(u, s);

  CDO<int> c(d_context.get());
  c = 4;

  EXPECT_EQ(c.d_pScope, u);
  EXPECT_NE(c.d_pContextObjRestore, nullptr);
  EXPECT_EQ(c.d_pContextObjNext, nullptr);
  EXPECT_EQ(c.d_ppContextObjPrev, &u->d_pContextObjList);

  d_context->pop();

  EXPECT_EQ(t->d_pContext, d_context.get());
  EXPECT_EQ(t->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(t->d_level, 1);
  EXPECT_EQ(t->d_pContextObjList, &b);

  EXPECT_EQ(a.d_pScope, t);
  EXPECT_NE(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  EXPECT_EQ(b.d_pScope, t);
  EXPECT_NE(b.d_pContextObjRestore, nullptr);
  EXPECT_EQ(b.d_pContextObjNext, &a);
  EXPECT_EQ(b.d_ppContextObjPrev, &t->d_pContextObjList);

  d_context->pop();

  EXPECT_EQ(s->d_pContext, d_context.get());
  EXPECT_EQ(s->d_pCMM, d_context->d_pCMM);
  EXPECT_EQ(s->d_level, 0);
  EXPECT_EQ(s->d_pContextObjList, &c);

  EXPECT_EQ(a.d_pScope, s);
  EXPECT_EQ(a.d_pContextObjRestore, nullptr);
  EXPECT_EQ(a.d_pContextObjNext, nullptr);
  EXPECT_EQ(a.d_ppContextObjPrev, &b.d_pContextObjNext);

  EXPECT_EQ(b.d_pScope, s);
  EXPECT_EQ(b.d_pContextObjRestore, nullptr);
  EXPECT_EQ(b.d_pContextObjNext, &a);
  EXPECT_EQ(b.d_ppContextObjPrev, &c.d_pContextObjNext);

  EXPECT_EQ(c.d_pScope, s);
  EXPECT_EQ(c.d_pContextObjRestore, nullptr);
  EXPECT_EQ(c.d_pContextObjNext, &b);
  EXPECT_EQ(c.d_ppContextObjPrev, &s->d_pContextObjList);
}
}  // namespace test
}  // namespace CVC4
