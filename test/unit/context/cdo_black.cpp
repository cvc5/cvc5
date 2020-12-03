/*********************                                                        */
/*! \file cdo_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDO<>.
 **
 ** Black box testing of CVC4::context::CDO<>.
 **/

#include <iostream>
#include <vector>

#include "base/check.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "test_context.h"

namespace CVC4 {

using namespace context;

namespace test {

class TestContextCDOBlack : public TestContext
{
};

TEST_F(TestContextCDOBlack, cdo)
{
  // Test that push/pop maintains the original value
  CDO<int> a1(d_context.get());
  a1 = 5;
  EXPECT_EQ(d_context->getLevel(), 0);
  d_context->push();
  a1 = 10;
  EXPECT_EQ(d_context->getLevel(), 1);
  EXPECT_EQ(a1, 10);
  d_context->pop();
  EXPECT_EQ(d_context->getLevel(), 0);
  EXPECT_EQ(a1, 5);
}

}  // namespace test
}  // namespace CVC4
