/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the Op class.
 */

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiWhiteOp : public TestApi
{
};

TEST_F(TestApiWhiteOp, opFromKind)
{
  Op plus(d_solver.getNodeManager(), ADD);
  ASSERT_FALSE(plus.isIndexed());
  ASSERT_EQ(0, plus.getNumIndices());
  ASSERT_EQ(plus, d_solver.mkOp(ADD));
}
}  // namespace test
}  // namespace cvc5::internal
