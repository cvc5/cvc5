/*********************                                                        */
/*! \file cdmap_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::context::CDMap<>.
 **
 ** White box testing of CVC4::context::CDMap<>.
 **/

#include "base/check.h"
#include "context/cdhashmap.h"
#include "test_context.h"

namespace CVC4 {

using namespace context;

namespace test {

class TestContextCDMapWhite : public TestContext
{
};

TEST_F(TestContextCDMapWhite, unreachable_save_and_restore)
{
  CDHashMap<int, int> map(d_context.get());

  ASSERT_NO_THROW(map.makeCurrent());

  ASSERT_DEATH(map.update(), "Unreachable code reached");

  ASSERT_DEATH(map.save(d_context->getCMM()), "Unreachable code reached");
  ASSERT_DEATH(map.restore(&map), "Unreachable code reached");

  d_context->push();
  ASSERT_DEATH(map.makeCurrent(), "Unreachable code reached");
}

}  // namespace test
}  // namespace CVC4
