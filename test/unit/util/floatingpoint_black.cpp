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
 * Black box testing of cvc5::FloatingPoint.
 */

#include "test.h"
#include "util/floatingpoint.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackFloatingPoint : public TestInternal
{
};

TEST_F(TestUtilBlackFloatingPoint, makeMinSubnormal)
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMinSubnormal(size16, true);
  ASSERT_TRUE(fp16.isSubnormal());
  FloatingPoint mfp16 = FloatingPoint::makeMinSubnormal(size16, false);
  ASSERT_TRUE(mfp16.isSubnormal());

  FloatingPoint fp32 = FloatingPoint::makeMinSubnormal(size32, true);
  ASSERT_TRUE(fp32.isSubnormal());
  FloatingPoint mfp32 = FloatingPoint::makeMinSubnormal(size32, false);
  ASSERT_TRUE(mfp32.isSubnormal());

  FloatingPoint fp64 = FloatingPoint::makeMinSubnormal(size64, true);
  ASSERT_TRUE(fp64.isSubnormal());
  FloatingPoint mfp64 = FloatingPoint::makeMinSubnormal(size64, false);
  ASSERT_TRUE(mfp64.isSubnormal());

  FloatingPoint fp128 = FloatingPoint::makeMinSubnormal(size128, true);
  ASSERT_TRUE(fp128.isSubnormal());
  FloatingPoint mfp128 = FloatingPoint::makeMinSubnormal(size128, false);
  ASSERT_TRUE(mfp128.isSubnormal());
}

TEST_F(TestUtilBlackFloatingPoint, makeMaxSubnormal)
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMaxSubnormal(size16, true);
  ASSERT_TRUE(fp16.isSubnormal());
  FloatingPoint mfp16 = FloatingPoint::makeMaxSubnormal(size16, false);
  ASSERT_TRUE(mfp16.isSubnormal());

  FloatingPoint fp32 = FloatingPoint::makeMaxSubnormal(size32, true);
  ASSERT_TRUE(fp32.isSubnormal());
  FloatingPoint mfp32 = FloatingPoint::makeMaxSubnormal(size32, false);
  ASSERT_TRUE(mfp32.isSubnormal());

  FloatingPoint fp64 = FloatingPoint::makeMaxSubnormal(size64, true);
  ASSERT_TRUE(fp64.isSubnormal());
  FloatingPoint mfp64 = FloatingPoint::makeMaxSubnormal(size64, false);
  ASSERT_TRUE(mfp64.isSubnormal());

  FloatingPoint fp128 = FloatingPoint::makeMaxSubnormal(size128, true);
  ASSERT_TRUE(fp128.isSubnormal());
  FloatingPoint mfp128 = FloatingPoint::makeMaxSubnormal(size128, false);
  ASSERT_TRUE(mfp128.isSubnormal());
}

TEST_F(TestUtilBlackFloatingPoint, makeMinNormal)
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMinNormal(size16, true);
  ASSERT_TRUE(fp16.isNormal());
  FloatingPoint mfp16 = FloatingPoint::makeMinNormal(size16, false);
  ASSERT_TRUE(mfp16.isNormal());

  FloatingPoint fp32 = FloatingPoint::makeMinNormal(size32, true);
  ASSERT_TRUE(fp32.isNormal());
  FloatingPoint mfp32 = FloatingPoint::makeMinNormal(size32, false);
  ASSERT_TRUE(mfp32.isNormal());

  FloatingPoint fp64 = FloatingPoint::makeMinNormal(size64, true);
  ASSERT_TRUE(fp64.isNormal());
  FloatingPoint mfp64 = FloatingPoint::makeMinNormal(size64, false);
  ASSERT_TRUE(mfp64.isNormal());

  FloatingPoint fp128 = FloatingPoint::makeMinNormal(size128, true);
  ASSERT_TRUE(fp128.isNormal());
  FloatingPoint mfp128 = FloatingPoint::makeMinNormal(size128, false);
  ASSERT_TRUE(mfp128.isNormal());
}

TEST_F(TestUtilBlackFloatingPoint, makeMaxNormal)
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMaxNormal(size16, true);
  ASSERT_TRUE(fp16.isNormal());
  FloatingPoint mfp16 = FloatingPoint::makeMaxNormal(size16, false);
  ASSERT_TRUE(mfp16.isNormal());

  FloatingPoint fp32 = FloatingPoint::makeMaxNormal(size32, true);
  ASSERT_TRUE(fp32.isNormal());
  FloatingPoint mfp32 = FloatingPoint::makeMaxNormal(size32, false);
  ASSERT_TRUE(mfp32.isNormal());

  FloatingPoint fp64 = FloatingPoint::makeMaxNormal(size64, true);
  ASSERT_TRUE(fp64.isNormal());
  FloatingPoint mfp64 = FloatingPoint::makeMaxNormal(size64, false);
  ASSERT_TRUE(mfp64.isNormal());

  FloatingPoint fp128 = FloatingPoint::makeMaxNormal(size128, true);
  ASSERT_TRUE(fp128.isNormal());
  FloatingPoint mfp128 = FloatingPoint::makeMaxNormal(size128, false);
  ASSERT_TRUE(mfp128.isNormal());
}
}  // namespace test
}  // namespace cvc5::internal
