/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the SynthResult class
 */

#include "test_api.h"

namespace cvc5 {

using namespace api;

namespace test {

class TestApiBlackSynthResult : public TestApi
{
};

TEST_F(TestApiBlackSynthResult, isNull)
{
  cvc5::api::SynthResult res_null;
  ASSERT_TRUE(res_null.isNull());
  ASSERT_FALSE(res_null.hasSolution());
  ASSERT_FALSE(res_null.hasNoSolution());
  ASSERT_FALSE(res_null.isUnknown());
}

}  // namespace test
}  // namespace cvc5
