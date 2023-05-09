/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Public-box testing of cvc5::Cardinality.
 */

#include <sstream>
#include <string>

#include "base/exception.h"
#include "test.h"
#include "util/cardinality.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackCardinality : public TestInternal
{
 protected:
  std::stringstream ss;
};

TEST_F(TestUtilBlackCardinality, cardinalities)
{
  Cardinality zero(0);
  Cardinality one(1);
  Cardinality two(2);

  Cardinality invalid(0);
  ASSERT_DEATH(invalid = Cardinality(-1), "card >= 0");
  ASSERT_DEATH(invalid = Cardinality(-2), "card >= 0");
  ASSERT_DEATH(invalid = Cardinality(Integer("-3983982192391747295721957")),
               "card >= 0");
  invalid = one;             // test assignment
  invalid = Cardinality(5);  // test assignment to temporary

  Cardinality copy(one);  // test copy
  Cardinality big(Integer("3983982192391747295721957"));
  Cardinality r(Cardinality::REALS);
  Cardinality i(Cardinality::INTEGERS);

  ASSERT_EQ(zero.compare(one), Cardinality::LESS);
  ASSERT_EQ(one.compare(two), Cardinality::LESS);
  ASSERT_EQ(two.compare(invalid), Cardinality::LESS);
  ASSERT_EQ(invalid.compare(big), Cardinality::LESS);
  ASSERT_EQ(big.compare(i), Cardinality::LESS);
  ASSERT_EQ(i.compare(r), Cardinality::LESS);

  ASSERT_NE(zero.compare(one), Cardinality::GREATER);
  ASSERT_NE(zero.compare(zero), Cardinality::GREATER);
  ASSERT_NE(one.compare(two), Cardinality::GREATER);
  ASSERT_NE(one.compare(one), Cardinality::GREATER);
  ASSERT_NE(two.compare(invalid), Cardinality::GREATER);
  ASSERT_NE(two.compare(two), Cardinality::GREATER);
  ASSERT_NE(invalid.compare(big), Cardinality::GREATER);
  ASSERT_NE(invalid.compare(invalid), Cardinality::GREATER);
  ASSERT_NE(big.compare(i), Cardinality::GREATER);
  ASSERT_NE(big.compare(big), Cardinality::GREATER);
  ASSERT_NE(i.compare(r), Cardinality::GREATER);
  ASSERT_NE(i.compare(i), Cardinality::GREATER);
  ASSERT_NE(r.compare(r), Cardinality::GREATER);

  ASSERT_EQ(zero.compare(zero), Cardinality::EQUAL);
  ASSERT_EQ(one.compare(one), Cardinality::EQUAL);
  ASSERT_EQ(two.compare(two), Cardinality::EQUAL);
  ASSERT_EQ(invalid.compare(invalid), Cardinality::EQUAL);
  ASSERT_EQ(copy.compare(copy), Cardinality::EQUAL);
  ASSERT_EQ(copy.compare(one), Cardinality::EQUAL);
  ASSERT_EQ(one.compare(copy), Cardinality::EQUAL);
  ASSERT_EQ(big.compare(big), Cardinality::UNKNOWN);
  ASSERT_EQ(i.compare(i), Cardinality::EQUAL);
  ASSERT_EQ(r.compare(r), Cardinality::EQUAL);

  ASSERT_NE(zero.compare(one), Cardinality::EQUAL);
  ASSERT_NE(one.compare(two), Cardinality::EQUAL);
  ASSERT_NE(two.compare(invalid), Cardinality::EQUAL);
  ASSERT_NE(copy.compare(r), Cardinality::EQUAL);
  ASSERT_NE(copy.compare(i), Cardinality::EQUAL);
  ASSERT_NE(big.compare(i), Cardinality::EQUAL);
  ASSERT_NE(i.compare(big), Cardinality::EQUAL);
  ASSERT_NE(big.compare(zero), Cardinality::EQUAL);
  ASSERT_NE(r.compare(i), Cardinality::EQUAL);
  ASSERT_NE(i.compare(r), Cardinality::EQUAL);

  ASSERT_EQ(r.compare(zero), Cardinality::GREATER);
  ASSERT_EQ(r.compare(one), Cardinality::GREATER);
  ASSERT_EQ(r.compare(two), Cardinality::GREATER);
  ASSERT_EQ(r.compare(copy), Cardinality::GREATER);
  ASSERT_EQ(r.compare(invalid), Cardinality::GREATER);
  ASSERT_EQ(r.compare(big), Cardinality::GREATER);
  ASSERT_EQ(r.compare(i), Cardinality::GREATER);
  ASSERT_NE(r.compare(r), Cardinality::GREATER);
  ASSERT_NE(r.compare(r), Cardinality::LESS);

  ASSERT_TRUE(zero.isFinite());
  ASSERT_TRUE(one.isFinite());
  ASSERT_TRUE(two.isFinite());
  ASSERT_TRUE(copy.isFinite());
  ASSERT_TRUE(invalid.isFinite());
  ASSERT_TRUE(big.isFinite());
  ASSERT_FALSE(i.isFinite());
  ASSERT_FALSE(r.isFinite());

  ASSERT_FALSE(zero.isLargeFinite());
  ASSERT_FALSE(one.isLargeFinite());
  ASSERT_FALSE(two.isLargeFinite());
  ASSERT_FALSE(copy.isLargeFinite());
  ASSERT_FALSE(invalid.isLargeFinite());
  ASSERT_TRUE(big.isLargeFinite());
  ASSERT_FALSE(i.isLargeFinite());
  ASSERT_FALSE(r.isLargeFinite());

  ASSERT_EQ(zero.getFiniteCardinality(), 0);
  ASSERT_EQ(one.getFiniteCardinality(), 1);
  ASSERT_EQ(two.getFiniteCardinality(), 2);
  ASSERT_EQ(copy.getFiniteCardinality(), 1);
  ASSERT_EQ(invalid.getFiniteCardinality(), 5);
  ASSERT_DEATH(big.getFiniteCardinality(), "!isLargeFinite\\(\\)");
  ASSERT_DEATH(i.getFiniteCardinality(), "getFiniteCardinality\\(\\)");
  ASSERT_DEATH(r.getFiniteCardinality(), "isFinite\\(\\)");

  ASSERT_DEATH(zero.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_DEATH(one.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_DEATH(two.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_DEATH(copy.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_DEATH(invalid.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_DEATH(big.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_TRUE(i.getBethNumber() == 0);
  ASSERT_TRUE(r.getBethNumber() == 1);

  ASSERT_NE(zero.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_NE(one.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_NE(two.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_NE(copy.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_NE(invalid.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_NE(big.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_NE(r.compare(Cardinality::INTEGERS), Cardinality::EQUAL);
  ASSERT_EQ(i.compare(Cardinality::INTEGERS), Cardinality::EQUAL);

  ASSERT_NE(zero.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_NE(one.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_NE(two.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_NE(copy.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_NE(invalid.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_NE(big.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_NE(i.compare(Cardinality::REALS), Cardinality::EQUAL);
  ASSERT_EQ(r.compare(Cardinality::REALS), Cardinality::EQUAL);

  // should work the other way too

  ASSERT_NE(Cardinality::INTEGERS.compare(zero), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::INTEGERS.compare(one), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::INTEGERS.compare(two), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::INTEGERS.compare(copy), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::INTEGERS.compare(invalid), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::INTEGERS.compare(big), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::INTEGERS.compare(r), Cardinality::EQUAL);
  ASSERT_EQ(Cardinality::INTEGERS.compare(i), Cardinality::EQUAL);

  ASSERT_NE(Cardinality::REALS.compare(zero), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::REALS.compare(one), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::REALS.compare(two), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::REALS.compare(copy), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::REALS.compare(invalid), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::REALS.compare(big), Cardinality::EQUAL);
  ASSERT_NE(Cardinality::REALS.compare(i), Cardinality::EQUAL);
  ASSERT_EQ(Cardinality::REALS.compare(r), Cardinality::EQUAL);

  // finite cardinal arithmetic

  ASSERT_EQ((zero + zero).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((zero * zero).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((zero ^ zero).compare(one), Cardinality::EQUAL);
  ASSERT_EQ((zero + one).compare(one), Cardinality::EQUAL);
  ASSERT_EQ((zero * one).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((zero ^ one).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((one + zero).compare(one), Cardinality::EQUAL);
  ASSERT_EQ((one * zero).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((one ^ zero).compare(one), Cardinality::EQUAL);
  ASSERT_EQ((two + two).compare(4), Cardinality::EQUAL);
  ASSERT_EQ((two ^ two).compare(4), Cardinality::EQUAL);
  ASSERT_EQ((two * two).compare(4), Cardinality::EQUAL);
  ASSERT_EQ((two += two).compare(4), Cardinality::EQUAL);
  ASSERT_EQ(two.compare(4), Cardinality::EQUAL);
  ASSERT_EQ((two = 2).compare(2), Cardinality::EQUAL);
  ASSERT_EQ(two.compare(2), Cardinality::EQUAL);
  ASSERT_EQ((two *= 2).compare(4), Cardinality::EQUAL);
  ASSERT_EQ(two.compare(4), Cardinality::EQUAL);
  ASSERT_EQ(((two = 2) ^= 2).compare(4), Cardinality::EQUAL);
  ASSERT_EQ(two.compare(4), Cardinality::EQUAL);
  ASSERT_EQ((two = 2).compare(2), Cardinality::EQUAL);

  // infinite cardinal arithmetic

  Cardinality x = i, y = Cardinality(2) ^ x, z = Cardinality(2) ^ y;

  ASSERT_TRUE(x.compare(i) == Cardinality::EQUAL
              && y.compare(r) == Cardinality::EQUAL);
  ASSERT_TRUE(x.compare(r) != Cardinality::EQUAL
              && y.compare(i) != Cardinality::EQUAL);
  ASSERT_TRUE(x.compare(z) != Cardinality::EQUAL
              && y.compare(z) != Cardinality::EQUAL);
  ASSERT_TRUE(x.isCountable() && !x.isFinite());
  ASSERT_FALSE(y.isCountable() && !y.isFinite());
  ASSERT_FALSE(z.isCountable() && !z.isFinite());

  ASSERT_EQ(big.compare(x), Cardinality::LESS);
  ASSERT_EQ(x.compare(y), Cardinality::LESS);
  ASSERT_EQ(y.compare(z), Cardinality::LESS);

  ASSERT_DEATH(big.getBethNumber(), "!isFinite\\(\\) && !isUnknown\\(\\)");
  ASSERT_EQ(x.getBethNumber(), 0);
  ASSERT_EQ(y.getBethNumber(), 1);
  ASSERT_EQ(z.getBethNumber(), 2);

  ASSERT_EQ((zero ^ x).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((one ^ x).compare(one), Cardinality::EQUAL);
  ASSERT_TRUE((two ^ x).compare(y) == Cardinality::EQUAL
              && (two ^ x).compare(x) != Cardinality::EQUAL);
  ASSERT_TRUE((big ^ x).compare(y) == Cardinality::EQUAL
              && (big ^ x).compare(x) != Cardinality::EQUAL);
  ASSERT_EQ((two ^ x).compare(big ^ x), Cardinality::EQUAL);

  ASSERT_EQ((x ^ zero).compare(one), Cardinality::EQUAL);
  ASSERT_EQ((x ^ one).compare(x), Cardinality::EQUAL);
  ASSERT_EQ((x ^ two).compare(x), Cardinality::EQUAL);
  ASSERT_EQ((x ^ big).compare(x), Cardinality::EQUAL);
  ASSERT_EQ((x ^ big).compare(x ^ two), Cardinality::EQUAL);

  ASSERT_EQ((zero ^ y).compare(zero), Cardinality::EQUAL);
  ASSERT_EQ((one ^ y).compare(one), Cardinality::EQUAL);
  ASSERT_TRUE((two ^ y).compare(x) != Cardinality::EQUAL
              && (two ^ y).compare(y) != Cardinality::EQUAL);
  ASSERT_TRUE((big ^ y).compare(y) != Cardinality::EQUAL
              && (big ^ y).compare(y) != Cardinality::EQUAL);
  ASSERT_EQ((big ^ y).getBethNumber(), 2);
  ASSERT_EQ((two ^ y).compare(big ^ y), Cardinality::EQUAL);

  ASSERT_EQ((y ^ zero).compare(one), Cardinality::EQUAL);
  ASSERT_EQ((y ^ one).compare(y), Cardinality::EQUAL);
  ASSERT_EQ((y ^ two).compare(y), Cardinality::EQUAL);
  ASSERT_EQ((y ^ big).compare(y), Cardinality::EQUAL);
  ASSERT_EQ((y ^ big).compare(y ^ two), Cardinality::EQUAL);

  ASSERT_EQ((x ^ x).compare(y), Cardinality::EQUAL);
  ASSERT_EQ((y ^ x).compare(y), Cardinality::EQUAL);
  ASSERT_EQ((x ^ y).compare(z), Cardinality::EQUAL);
  ASSERT_EQ((y ^ y).compare(z), Cardinality::EQUAL);
  ASSERT_EQ((z ^ x).compare(z), Cardinality::EQUAL);
  ASSERT_EQ((z ^ y).compare(z), Cardinality::EQUAL);
  ASSERT_EQ((zero ^ z).compare(0), Cardinality::EQUAL);
  ASSERT_EQ((z ^ zero).compare(1), Cardinality::EQUAL);
  ASSERT_EQ((z ^ 0).compare(1), Cardinality::EQUAL);
  ASSERT_EQ((two ^ z).compare(z), Cardinality::GREATER);
  ASSERT_EQ((big ^ z).compare(two ^ z), Cardinality::EQUAL);
  ASSERT_EQ((x ^ z).compare(two ^ z), Cardinality::EQUAL);
  ASSERT_EQ((y ^ z).compare(x ^ z), Cardinality::EQUAL);
  ASSERT_EQ((z ^ z).compare(x ^ z), Cardinality::EQUAL);
  ASSERT_EQ((z ^ z).getBethNumber(), 3);
}
}  // namespace test
}  // namespace cvc5::internal
