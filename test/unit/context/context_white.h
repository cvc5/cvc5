/*********************                                                        */
/*! \file context_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::context::Context.
 **
 ** White box testing of CVC4::context::Context.
 **/

#include <cxxtest/TestSuite.h>

#include "base/check.h"
#include "context/cdo.h"
#include "context/context.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class ContextWhite : public CxxTest::TestSuite {
private:

  Context* d_context;

 public:
  void setUp() override { d_context = new Context; }

  void tearDown() override { delete d_context; }

  void testContextSimple()
  {
    Scope* s = d_context->getTopScope();

    TS_ASSERT(s == d_context->getBottomScope());
    TS_ASSERT(d_context->getLevel() == 0);
    TS_ASSERT(d_context->d_scopeList.size() == 1);

    TS_ASSERT(s->d_pContext == d_context);
    TS_ASSERT(s->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(s->d_level == 0);
    TS_ASSERT(s->d_pContextObjList == NULL);

    CDO<int> a(d_context);

    TS_ASSERT(s->d_pContext == d_context);
    TS_ASSERT(s->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(s->d_level == 0);
    TS_ASSERT(s->d_pContextObjList == &a);

    TS_ASSERT(a.d_pScope == s);
    TS_ASSERT(a.d_pContextObjRestore == NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &s->d_pContextObjList);

    CDO<int> b(d_context);

    TS_ASSERT(s->d_pContext == d_context);
    TS_ASSERT(s->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(s->d_level == 0);
    TS_ASSERT(s->d_pContextObjList == &b);

    TS_ASSERT(a.d_pScope == s);
    TS_ASSERT(a.d_pContextObjRestore == NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &b.d_pContextObjNext);

    TS_ASSERT(b.d_pScope == s);
    TS_ASSERT(b.d_pContextObjRestore == NULL);
    TS_ASSERT(b.d_pContextObjNext == &a);
    TS_ASSERT(b.d_ppContextObjPrev == &s->d_pContextObjList);

    d_context->push();
    Scope* t = d_context->getTopScope();
    TS_ASSERT(s != t);

    TS_ASSERT(s == d_context->getBottomScope());
    TS_ASSERT(d_context->getLevel() == 1);
    TS_ASSERT(d_context->d_scopeList.size() == 2);

    TS_ASSERT(s->d_pContext == d_context);
    TS_ASSERT(s->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(s->d_level == 0);
    TS_ASSERT(s->d_pContextObjList == &b);

    TS_ASSERT(t->d_pContext == d_context);
    TS_ASSERT(t->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(t->d_level == 1);
    TS_ASSERT(t->d_pContextObjList == NULL);

    TS_ASSERT(a.d_pScope == s);
    TS_ASSERT(a.d_pContextObjRestore == NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &b.d_pContextObjNext);

    TS_ASSERT(b.d_pScope == s);
    TS_ASSERT(b.d_pContextObjRestore == NULL);
    TS_ASSERT(b.d_pContextObjNext == &a);
    TS_ASSERT(b.d_ppContextObjPrev == &s->d_pContextObjList);

    a = 5;

    TS_ASSERT(t->d_pContext == d_context);
    TS_ASSERT(t->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(t->d_level == 1);
    TS_ASSERT(t->d_pContextObjList == &a);

    TS_ASSERT(a.d_pScope == t);
    TS_ASSERT(a.d_pContextObjRestore != NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &t->d_pContextObjList);

    b = 3;

    TS_ASSERT(t->d_pContext == d_context);
    TS_ASSERT(t->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(t->d_level == 1);
    TS_ASSERT(t->d_pContextObjList == &b);

    TS_ASSERT(a.d_pScope == t);
    TS_ASSERT(a.d_pContextObjRestore != NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &b.d_pContextObjNext);

    TS_ASSERT(b.d_pScope == t);
    TS_ASSERT(b.d_pContextObjRestore != NULL);
    TS_ASSERT(b.d_pContextObjNext == &a);
    TS_ASSERT(b.d_ppContextObjPrev == &t->d_pContextObjList);

    d_context->push();
    Scope* u = d_context->getTopScope();
    TS_ASSERT(u != t);
    TS_ASSERT(u != s);

    CDO<int> c(d_context);
    c = 4;

    TS_ASSERT(c.d_pScope == u);
    TS_ASSERT(c.d_pContextObjRestore != NULL);
    TS_ASSERT(c.d_pContextObjNext == NULL);
    TS_ASSERT(c.d_ppContextObjPrev == &u->d_pContextObjList);

    d_context->pop();

    TS_ASSERT(t->d_pContext == d_context);
    TS_ASSERT(t->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(t->d_level == 1);
    TS_ASSERT(t->d_pContextObjList == &b);

    TS_ASSERT(a.d_pScope == t);
    TS_ASSERT(a.d_pContextObjRestore != NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &b.d_pContextObjNext);

    TS_ASSERT(b.d_pScope == t);
    TS_ASSERT(b.d_pContextObjRestore != NULL);
    TS_ASSERT(b.d_pContextObjNext == &a);
    TS_ASSERT(b.d_ppContextObjPrev == &t->d_pContextObjList);

    d_context->pop();

    TS_ASSERT(s->d_pContext == d_context);
    TS_ASSERT(s->d_pCMM == d_context->d_pCMM);
    TS_ASSERT(s->d_level == 0);
    TS_ASSERT(s->d_pContextObjList == &c);

    TS_ASSERT(a.d_pScope == s);
    TS_ASSERT(a.d_pContextObjRestore == NULL);
    TS_ASSERT(a.d_pContextObjNext == NULL);
    TS_ASSERT(a.d_ppContextObjPrev == &b.d_pContextObjNext);

    TS_ASSERT(b.d_pScope == s);
    TS_ASSERT(b.d_pContextObjRestore == NULL);
    TS_ASSERT(b.d_pContextObjNext == &a);
    TS_ASSERT(b.d_ppContextObjPrev == &c.d_pContextObjNext);

    TS_ASSERT(c.d_pScope == s);
    TS_ASSERT(c.d_pContextObjRestore == NULL);
    TS_ASSERT(c.d_pContextObjNext == &b);
    TS_ASSERT(c.d_ppContextObjPrev == &s->d_pContextObjList);
  }
};
