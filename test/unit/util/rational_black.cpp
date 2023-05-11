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
 * Black box testing of cvc5::Rational.
 */

#include <sstream>

#include "test.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackRational : public TestInternal
{
};

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
}  // namespace cvc5::internal
