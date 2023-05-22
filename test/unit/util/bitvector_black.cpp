/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::BitVector.
 */

#include <sstream>

#include "test.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackBitVector : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_zero = BitVector(4);
    d_one = BitVector::mkOne(4);
    d_two = BitVector("0010", 2);
    d_neg_one = BitVector(4, Integer(-1));
    d_ones = BitVector::mkOnes(4);
  }

  BitVector d_zero;
  BitVector d_one;
  BitVector d_two;
  BitVector d_neg_one;
  BitVector d_ones;
};

TEST_F(TestUtilBlackBitVector, string_constructor)
{
  BitVector b1("0101", 2);
  ASSERT_EQ(4u, b1.getSize());
  ASSERT_EQ("0101", b1.toString());
  ASSERT_EQ("5", b1.toString(10));
  ASSERT_EQ("5", b1.toString(16));

  BitVector b2("000001", 2);
  ASSERT_EQ(6u, b2.getSize());
  ASSERT_EQ("000001", b2.toString());
  ASSERT_EQ("1", b2.toString(10));
  ASSERT_EQ("1", b2.toString(16));

  BitVector b3("7f", 16);
  ASSERT_EQ(8u, b3.getSize());
  ASSERT_EQ("01111111", b3.toString());
  ASSERT_EQ("127", b3.toString(10));
  ASSERT_EQ("7f", b3.toString(16));

  BitVector b4("01a", 16);
  ASSERT_EQ(12u, b4.getSize());
  ASSERT_EQ("000000011010", b4.toString());
  ASSERT_EQ("26", b4.toString(10));
  ASSERT_EQ("1a", b4.toString(16));

  ASSERT_DEATH(BitVector("-4", 10), "num\\[0\\] != '-'");
  ASSERT_DEATH(BitVector("-0010", 2), "num\\[0\\] != '-'");
  ASSERT_DEATH(BitVector("-3210", 4), "base == 2");
  ASSERT_EQ(3, BitVector("4", 10).getSize());
}

TEST_F(TestUtilBlackBitVector, conversions)
{
  ASSERT_EQ(d_two.toSignedInteger(), Integer(2));
  ASSERT_EQ(d_neg_one.toString(), "1111");
  ASSERT_EQ(d_neg_one.getValue(), Integer(15));
  ASSERT_EQ(d_neg_one.getSize(), 4);
  ASSERT_EQ(d_neg_one.toInteger(), Integer(15));
  ASSERT_EQ(d_neg_one.toSignedInteger(), Integer(-1));

  ASSERT_EQ(d_zero.hash(), (d_one - d_one).hash());
  ASSERT_NE(d_neg_one.hash(), d_zero.hash());
}

TEST_F(TestUtilBlackBitVector, setBit_getBit)
{
  BitVector ones(d_one);
  ASSERT_EQ(ones.setBit(1, true).setBit(2, true).setBit(3, true), d_ones);

  BitVector zero(d_ones);
  ASSERT_EQ(
      zero.setBit(0, false).setBit(1, false).setBit(2, false).setBit(3, false),
      d_zero);

  ones = d_ones;
  ASSERT_EQ(ones.setBit(0, false).setBit(0, true), d_ones);

  BitVector not_one(d_ones);
  ASSERT_EQ(not_one.setBit(0, false), ~BitVector::mkOne(d_one.getSize()));

  ASSERT_TRUE(d_ones.isBitSet(3));
  ASSERT_FALSE(d_two.isBitSet(3));

  ASSERT_EQ(d_one.getValue(), Integer(1));
  ASSERT_EQ(d_zero.isPow2(), 0);
  ASSERT_EQ(d_one.isPow2(), 1);
  ASSERT_EQ(d_two.isPow2(), 2);
  ASSERT_EQ(d_ones.isPow2(), 0);
}

TEST_F(TestUtilBlackBitVector, concat_extract)
{
  BitVector b = d_one.concat(d_zero);
  ASSERT_EQ(b.toString(), "00010000");
  ASSERT_EQ(b.extract(7, 4), d_one);
  ASSERT_DEATH(b.extract(4, 7), "low <= high");
  ASSERT_DEATH(b.extract(8, 3), "high < d_size");
  ASSERT_EQ(b.concat(BitVector()), b);
}

TEST_F(TestUtilBlackBitVector, comparisons)
{
  ASSERT_NE(d_zero, d_one);
  ASSERT_TRUE(d_neg_one > d_zero);
  ASSERT_TRUE(d_neg_one >= d_zero);
  ASSERT_TRUE(d_neg_one >= d_neg_one);
  ASSERT_TRUE(d_neg_one == d_neg_one);
  ASSERT_TRUE(d_zero.unsignedLessThan(d_neg_one));
  ASSERT_TRUE(d_zero.unsignedLessThanEq(d_neg_one));
  ASSERT_TRUE(d_zero.unsignedLessThanEq(d_zero));
  ASSERT_TRUE(d_zero < d_neg_one);
  ASSERT_TRUE(d_zero <= d_neg_one);
  ASSERT_TRUE(d_zero <= d_zero);
  ASSERT_TRUE(d_neg_one.signedLessThan(d_zero));
  ASSERT_TRUE(d_neg_one.signedLessThanEq(d_zero));
  ASSERT_TRUE(d_neg_one.signedLessThanEq(d_neg_one));

  BitVector b = d_neg_one.concat(d_neg_one);
  ASSERT_DEATH(b.unsignedLessThan(d_neg_one), "d_size == y.d_size");
  ASSERT_DEATH(d_neg_one.unsignedLessThanEq(b), "d_size == y.d_size");
  ASSERT_DEATH(b.signedLessThan(d_neg_one), "d_size == y.d_size");
  ASSERT_DEATH(d_neg_one.signedLessThanEq(b), "d_size == y.d_size");
}

TEST_F(TestUtilBlackBitVector, bitwise_operators)
{
  ASSERT_EQ((d_one ^ d_neg_one).toString(), "1110");
  ASSERT_EQ((d_two | d_one).toString(), "0011");
  ASSERT_EQ((d_neg_one & d_two).toString(), "0010");
  ASSERT_EQ((~d_two).toString(), "1101");
}

TEST_F(TestUtilBlackBitVector, arithmetic)
{
  ASSERT_EQ(d_neg_one + d_one, d_zero);
  ASSERT_EQ((d_neg_one - d_one).getValue(), Integer(14));
  ASSERT_EQ((-d_neg_one).getValue(), Integer(1));

  ASSERT_EQ((d_two * (d_two + d_one)).getValue(), Integer(6));

  ASSERT_EQ(d_two.unsignedDivTotal(d_zero), d_neg_one);
  ASSERT_EQ(d_neg_one.unsignedDivTotal(d_two).getValue(), Integer(7));

  ASSERT_EQ(d_two.unsignedRemTotal(d_zero), d_two);
  ASSERT_EQ(d_neg_one.unsignedRemTotal(d_two), d_one);

  BitVector b = d_neg_one.concat(d_neg_one);
  ASSERT_DEATH(b + d_neg_one, "a.getSize\\(\\) == b.getSize\\(\\)");
  ASSERT_DEATH(d_neg_one * b, "a.getSize\\(\\) == b.getSize\\(\\)");
  ASSERT_DEATH(b.unsignedDivTotal(d_neg_one), "d_size == y\\.d_size");
  ASSERT_DEATH(d_neg_one.unsignedRemTotal(b), "d_size == y\\.d_size");
}

TEST_F(TestUtilBlackBitVector, extend_operators)
{
  ASSERT_EQ(d_one.zeroExtend(4), d_zero.concat(d_one));
  ASSERT_EQ(d_one.zeroExtend(0), d_one);
  ASSERT_EQ(d_neg_one.signExtend(4), d_neg_one.concat(d_neg_one));
  ASSERT_EQ(d_one.signExtend(4), d_zero.concat(d_one));
  ASSERT_EQ(d_one.signExtend(0), d_one);
}

TEST_F(TestUtilBlackBitVector, shift_operators)
{
  ASSERT_EQ(d_one.leftShift(d_one), d_two);
  ASSERT_EQ(d_one.leftShift(d_neg_one), d_zero);
  ASSERT_EQ(d_one.leftShift(d_zero), d_one);

  ASSERT_EQ(d_two.logicalRightShift(d_one), d_one);
  ASSERT_EQ(d_two.logicalRightShift(d_neg_one), d_zero);

  ASSERT_EQ(d_two.arithRightShift(d_one), d_one);
  ASSERT_EQ(d_neg_one.arithRightShift(d_one), d_neg_one);
  ASSERT_EQ(d_neg_one.arithRightShift(d_neg_one), d_neg_one);
  ASSERT_EQ(d_two.arithRightShift(d_neg_one), d_zero);
}

TEST_F(TestUtilBlackBitVector, static_helpers)
{
  ASSERT_EQ(BitVector::mkZero(4), d_zero);
  ASSERT_EQ(BitVector::mkOne(4), d_one);
  ASSERT_EQ(BitVector::mkOnes(4), d_neg_one);
  ASSERT_EQ(BitVector::mkMinSigned(4).toSignedInteger(), Integer(-8));
  ASSERT_EQ(BitVector::mkMaxSigned(4).toSignedInteger(), Integer(7));
}
}  // namespace test
}  // namespace cvc5::internal
