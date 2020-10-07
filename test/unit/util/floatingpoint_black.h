/*********************                                                        */
/*! \file floatingpoint_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::FloatingPoint.
 **
 ** Black box testing of CVC4::FloatingPoint.
 **/
#include <cxxtest/TestSuite.h>

#include "util/floatingpoint.h"

using namespace CVC4;

class FloatingPointBlack : public CxxTest::TestSuite
{
 public:
  void testMakeMinSubnormal();
  void testMakeMaxSubnormal();
  void testMakeMinNormal();
  void testMakeMaxNormal();
};

void FloatingPointBlack::testMakeMinSubnormal()
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMinSubnormal(size16, true);
  TS_ASSERT(fp16.isSubnormal());
  FloatingPoint mfp16 = FloatingPoint::makeMinSubnormal(size16, false);
  TS_ASSERT(mfp16.isSubnormal());

  FloatingPoint fp32 = FloatingPoint::makeMinSubnormal(size32, true);
  TS_ASSERT(fp32.isSubnormal());
  FloatingPoint mfp32 = FloatingPoint::makeMinSubnormal(size32, false);
  TS_ASSERT(mfp32.isSubnormal());

  FloatingPoint fp64 = FloatingPoint::makeMinSubnormal(size64, true);
  TS_ASSERT(fp64.isSubnormal());
  FloatingPoint mfp64 = FloatingPoint::makeMinSubnormal(size64, false);
  TS_ASSERT(mfp64.isSubnormal());

  FloatingPoint fp128 = FloatingPoint::makeMinSubnormal(size128, true);
  TS_ASSERT(fp128.isSubnormal());
  FloatingPoint mfp128 = FloatingPoint::makeMinSubnormal(size128, false);
  TS_ASSERT(mfp128.isSubnormal());
}

void FloatingPointBlack::testMakeMaxSubnormal()
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMaxSubnormal(size16, true);
  TS_ASSERT(fp16.isSubnormal());
  FloatingPoint mfp16 = FloatingPoint::makeMaxSubnormal(size16, false);
  TS_ASSERT(mfp16.isSubnormal());

  FloatingPoint fp32 = FloatingPoint::makeMaxSubnormal(size32, true);
  TS_ASSERT(fp32.isSubnormal());
  FloatingPoint mfp32 = FloatingPoint::makeMaxSubnormal(size32, false);
  TS_ASSERT(mfp32.isSubnormal());

  FloatingPoint fp64 = FloatingPoint::makeMaxSubnormal(size64, true);
  TS_ASSERT(fp64.isSubnormal());
  FloatingPoint mfp64 = FloatingPoint::makeMaxSubnormal(size64, false);
  TS_ASSERT(mfp64.isSubnormal());

  FloatingPoint fp128 = FloatingPoint::makeMaxSubnormal(size128, true);
  TS_ASSERT(fp128.isSubnormal());
  FloatingPoint mfp128 = FloatingPoint::makeMaxSubnormal(size128, false);
  TS_ASSERT(mfp128.isSubnormal());
}

void FloatingPointBlack::testMakeMinNormal()
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMinNormal(size16, true);
  TS_ASSERT(fp16.isNormal());
  FloatingPoint mfp16 = FloatingPoint::makeMinNormal(size16, false);
  TS_ASSERT(mfp16.isNormal());

  FloatingPoint fp32 = FloatingPoint::makeMinNormal(size32, true);
  TS_ASSERT(fp32.isNormal());
  FloatingPoint mfp32 = FloatingPoint::makeMinNormal(size32, false);
  TS_ASSERT(mfp32.isNormal());

  FloatingPoint fp64 = FloatingPoint::makeMinNormal(size64, true);
  TS_ASSERT(fp64.isNormal());
  FloatingPoint mfp64 = FloatingPoint::makeMinNormal(size64, false);
  TS_ASSERT(mfp64.isNormal());

  FloatingPoint fp128 = FloatingPoint::makeMinNormal(size128, true);
  TS_ASSERT(fp128.isNormal());
  FloatingPoint mfp128 = FloatingPoint::makeMinNormal(size128, false);
  TS_ASSERT(mfp128.isNormal());
}

void FloatingPointBlack::testMakeMaxNormal()
{
  FloatingPointSize size16(5, 11);
  FloatingPointSize size32(8, 24);
  FloatingPointSize size64(11, 53);
  FloatingPointSize size128(15, 113);

  FloatingPoint fp16 = FloatingPoint::makeMaxNormal(size16, true);
  TS_ASSERT(fp16.isNormal());
  FloatingPoint mfp16 = FloatingPoint::makeMaxNormal(size16, false);
  TS_ASSERT(mfp16.isNormal());

  FloatingPoint fp32 = FloatingPoint::makeMaxNormal(size32, true);
  TS_ASSERT(fp32.isNormal());
  FloatingPoint mfp32 = FloatingPoint::makeMaxNormal(size32, false);
  TS_ASSERT(mfp32.isNormal());

  FloatingPoint fp64 = FloatingPoint::makeMaxNormal(size64, true);
  TS_ASSERT(fp64.isNormal());
  FloatingPoint mfp64 = FloatingPoint::makeMaxNormal(size64, false);
  TS_ASSERT(mfp64.isNormal());

  FloatingPoint fp128 = FloatingPoint::makeMaxNormal(size128, true);
  TS_ASSERT(fp128.isNormal());
  FloatingPoint mfp128 = FloatingPoint::makeMaxNormal(size128, false);
  TS_ASSERT(mfp128.isNormal());
}
