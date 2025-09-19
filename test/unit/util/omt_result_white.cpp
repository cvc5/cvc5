/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of the internal OmtResult class 
 */

#include "test.h"
#include <util/omt_result.h>

namespace cvc5::internal {
namespace test {

class TestUtilWhiteOmtResult : public TestInternal
{
};

TEST_F(TestUtilWhiteOmtResult, isNull)
{
  OmtResult res_null;
  ASSERT_TRUE(res_null.getStatus() == OmtResult::NONE);
  ASSERT_FALSE(res_null.getStatus() == OmtResult::OPTIMAL);
  ASSERT_FALSE(res_null.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_FALSE(res_null.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_FALSE(res_null.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_FALSE(res_null.getStatus() == OmtResult::UNSAT); 
  ASSERT_FALSE(res_null.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, isOptimal)
{
  OmtResult res = OmtResult(OmtResult::Status::OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NONE);
  ASSERT_TRUE(res.getStatus() == OmtResult::OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNSAT); 
  ASSERT_FALSE(res.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, isLimitOptimal)
{
  OmtResult res = OmtResult(OmtResult::Status::LIMIT_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NONE);
  ASSERT_FALSE(res.getStatus() == OmtResult::OPTIMAL);
  ASSERT_TRUE(res.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNSAT); 
  ASSERT_FALSE(res.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, isNonOptimal)
{
  OmtResult res = OmtResult(OmtResult::Status::NON_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NONE);
  ASSERT_FALSE(res.getStatus() == OmtResult::OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_TRUE(res.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNSAT); 
  ASSERT_FALSE(res.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, isUnbounded)
{
  OmtResult res = OmtResult(OmtResult::Status::UNBOUNDED);
  ASSERT_FALSE(res.getStatus() == OmtResult::NONE);
  ASSERT_FALSE(res.getStatus() == OmtResult::OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_TRUE(res.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNSAT); 
  ASSERT_FALSE(res.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, isUnsat)
{
  OmtResult res = OmtResult(OmtResult::Status::UNSAT);
  ASSERT_FALSE(res.getStatus() == OmtResult::NONE);
  ASSERT_FALSE(res.getStatus() == OmtResult::OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_TRUE(res.getStatus() == OmtResult::UNSAT); 
  ASSERT_FALSE(res.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, isUnknown)
{
  OmtResult res = OmtResult(OmtResult::Status::UNKNOWN);
  ASSERT_FALSE(res.getStatus() == OmtResult::NONE);
  ASSERT_FALSE(res.getStatus() == OmtResult::OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::LIMIT_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::NON_OPTIMAL);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNBOUNDED);
  ASSERT_FALSE(res.getStatus() == OmtResult::UNSAT); 
  ASSERT_TRUE(res.getStatus() == OmtResult::UNKNOWN); 
}

TEST_F(TestUtilWhiteOmtResult, statusStreamOutput)
{
  {
    OmtResult ss = OmtResult(OmtResult::Status::NONE);
    ASSERT_EQ(ss.toString(), "(NONE)");
  }
  {
    OmtResult ss = OmtResult(OmtResult::Status::OPTIMAL);
    ASSERT_EQ(ss.toString(), "(OPTIMAL)");
  }
  {
    OmtResult ss = OmtResult(OmtResult::Status::LIMIT_OPTIMAL);
    ASSERT_EQ(ss.toString(), "(LIMIT_OPTIMAL)");
  }
  {
    OmtResult ss = OmtResult(OmtResult::Status::NON_OPTIMAL);
    ASSERT_EQ(ss.toString(), "(NON_OPTIMAL)");
  }
  {
    OmtResult ss = OmtResult(OmtResult::Status::UNBOUNDED);
    ASSERT_EQ(ss.toString(), "(UNBOUNDED)");
  }
  {
    OmtResult ss = OmtResult(OmtResult::Status::UNSAT);
    ASSERT_EQ(ss.toString(), "(UNSAT)");
  }
  {
    OmtResult ss = OmtResult(OmtResult::Status::UNKNOWN);
    ASSERT_EQ(ss.toString(), "(UNKNOWN)");
  }
}

TEST_F(TestUtilWhiteOmtResult, equalResults)
{
  OmtResult res_null = OmtResult();
  OmtResult res_optimal = OmtResult(OmtResult::Status::OPTIMAL);
  OmtResult res_limit_optimal = OmtResult(OmtResult::Status::LIMIT_OPTIMAL);
  OmtResult res_non_optimal = OmtResult(OmtResult::Status::NON_OPTIMAL);
  OmtResult res_unbounded = OmtResult(OmtResult::Status::UNBOUNDED);
  OmtResult res_unsat = OmtResult(OmtResult::Status::UNSAT);
  OmtResult res_unknown = OmtResult(OmtResult::Status::UNKNOWN);

  ASSERT_EQ(res_optimal, res_optimal);
  ASSERT_EQ(res_limit_optimal, res_limit_optimal);
  ASSERT_EQ(res_non_optimal, res_non_optimal);
  ASSERT_EQ(res_unbounded, res_unbounded);
  ASSERT_EQ(res_unsat, res_unsat);
  ASSERT_EQ(res_unknown, res_unknown);
  ASSERT_EQ(res_null, res_null);

  ASSERT_NE(res_null, res_optimal);
  ASSERT_NE(res_null, res_limit_optimal);
  ASSERT_NE(res_null, res_non_optimal);
  ASSERT_NE(res_null, res_unbounded);
  ASSERT_NE(res_null, res_unsat);
  ASSERT_NE(res_null, res_unknown);

  ASSERT_NE(res_optimal, res_limit_optimal);
  ASSERT_NE(res_optimal, res_non_optimal);
  ASSERT_NE(res_optimal, res_unbounded);
  ASSERT_NE(res_optimal, res_unsat);
  ASSERT_NE(res_optimal, res_unknown);
  ASSERT_NE(res_limit_optimal, res_non_optimal);
  ASSERT_NE(res_limit_optimal, res_unbounded);
  ASSERT_NE(res_limit_optimal, res_unsat);
  ASSERT_NE(res_limit_optimal, res_unknown);
  ASSERT_NE(res_non_optimal, res_unbounded);
  ASSERT_NE(res_non_optimal, res_unsat);
  ASSERT_NE(res_non_optimal, res_unknown);
  ASSERT_NE(res_unbounded, res_unsat);
  ASSERT_NE(res_unbounded, res_unknown);
  ASSERT_NE(res_unsat, res_unknown);
}

}  // namespace test
}  // namespace cvc5::internal
