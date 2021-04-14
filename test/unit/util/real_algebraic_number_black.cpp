/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::RealAlgebraicNumber.
 */

#include "test.h"
#include "util/real_algebraic_number.h"

namespace cvc5 {
namespace test {

#ifndef CVC5_POLY_IMP
#error "This unit test should only be enabled for CVC5_POLY_IMP"
#endif

class TestUtilBlackRealAlgebraicNumber : public TestInternal
{
};

TEST_F(TestUtilBlackRealAlgebraicNumber, creation)
{
  ASSERT_TRUE(isZero(RealAlgebraicNumber()));
  ASSERT_TRUE(isOne(RealAlgebraicNumber(Integer(1))));
  ASSERT_FALSE(isOne(RealAlgebraicNumber(Rational(2))));
  RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
  ASSERT_TRUE(RealAlgebraicNumber(Integer(1)) < sqrt2);
  ASSERT_TRUE(sqrt2 < RealAlgebraicNumber(Integer(2)));
}

TEST_F(TestUtilBlackRealAlgebraicNumber, comprison)
{
  RealAlgebraicNumber msqrt3({-3, 0, 1}, -2, -1);
  RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
  RealAlgebraicNumber zero;
  RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
  RealAlgebraicNumber sqrt3({-3, 0, 1}, 1, 2);

  ASSERT_TRUE(msqrt3 < msqrt2);
  ASSERT_TRUE(msqrt3 < zero);
  ASSERT_TRUE(msqrt3 < sqrt2);
  ASSERT_TRUE(msqrt3 < sqrt3);
  ASSERT_TRUE(msqrt2 < zero);
  ASSERT_TRUE(msqrt2 < sqrt2);
  ASSERT_TRUE(msqrt2 < sqrt3);
  ASSERT_TRUE(zero < sqrt2);
  ASSERT_TRUE(zero < sqrt3);
  ASSERT_TRUE(sqrt2 < sqrt3);
}

TEST_F(TestUtilBlackRealAlgebraicNumber, sgn)
{
  RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
  RealAlgebraicNumber zero;
  RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);

  ASSERT_EQ(sgn(msqrt2), -1);
  ASSERT_EQ(sgn(zero), 0);
  ASSERT_EQ(sgn(sqrt2), 1);
}

TEST_F(TestUtilBlackRealAlgebraicNumber, arithmetic)
{
  RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
  RealAlgebraicNumber zero;
  RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);

  ASSERT_EQ(msqrt2 + sqrt2, zero);
  ASSERT_EQ(-msqrt2, sqrt2);
  ASSERT_EQ(-msqrt2 + sqrt2, sqrt2 + sqrt2);
  ASSERT_EQ(msqrt2 * sqrt2, RealAlgebraicNumber(Integer(-2)));
}
}  // namespace test
}  // namespace cvc5
