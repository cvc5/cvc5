/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Makai Mann
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the Op class.
 */

#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiWhiteOp : public TestApi
{
};

TEST_F(TestApiWhiteOp, opFromKind)
{
  Op plus(&d_solver, ADD);
  ASSERT_FALSE(plus.isIndexed());
  ASSERT_THROW(plus.getIndices<uint32_t>(), CVC5ApiException);
  ASSERT_EQ(plus, d_solver.mkOp(ADD));
}
}  // namespace test
}  // namespace cvc5
