/*********************                                                        */
/*! \file cdo_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDO<>.
 **
 ** Black box testing of CVC4::context::CDO<>.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <vector>

#include "base/check.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/context.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class CDOBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

 public:
  void setUp() override { d_context = new Context; }

  void tearDown() override { delete d_context; }

  void testIntCDO()
  {
    // Test that push/pop maintains the original value
    CDO<int> a1(d_context);
    a1 = 5;
    TS_ASSERT(d_context->getLevel() == 0);
    d_context->push();
    a1 = 10;
    TS_ASSERT(d_context->getLevel() == 1);
    TS_ASSERT(a1 == 10);
    d_context->pop();
    TS_ASSERT(d_context->getLevel() == 0);
    TS_ASSERT(a1 == 5);
  }
};
