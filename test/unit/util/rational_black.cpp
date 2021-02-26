/*********************                                                        */
/*! \file rational_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Rational.
 **
 ** Black box testing of CVC4::Rational.
 **/

#include <sstream>

#include "test.h"
#include "util/rational.h"

namespace CVC4 {
namespace test {

class TestUtilBlackRational : public TestInternal
{
 protected:
  static const char* can_reduce_val;
};

const char* TestUtilBlackRational::can_reduce_val =
    "4547897890548754897897897897890789078907890/54878902347890234";

TEST_F(TestUtilBlackRational, fromDecimal)
{
  ASSERT_EQ(Rational(0, 1), Rational::fromDecimal("0"));
  ASSERT_EQ(Rational(1, 1), Rational::fromDecimal("1"));
  ASSERT_EQ(Rational(-1, 1), Rational::fromDecimal("-1"));
  ASSERT_EQ(Rational(3, 2), Rational::fromDecimal("1.5"));
  ASSERT_EQ(Rational(-3, 2), Rational::fromDecimal("-1.5"));
  ASSERT_EQ(Rational(7, 10), Rational::fromDecimal(".7"));
  ASSERT_EQ(Rational(-7, 10), Rational::fromDecimal("-.7"));
  ASSERT_EQ(Rational(5, 1), Rational::fromDecimal("5."));
  ASSERT_EQ(Rational(-5, 1), Rational::fromDecimal("-5."));
  ASSERT_EQ(Rational(12345, 100), Rational::fromDecimal("123.45"));

  ASSERT_THROW(Rational::fromDecimal("1.2.3");, std::invalid_argument);
  ASSERT_THROW(Rational::fromDecimal("1.2/3");, std::invalid_argument);
  ASSERT_THROW(Rational::fromDecimal("Hello, world!");, std::invalid_argument);
}
}  // namespace test
}  // namespace CVC4
