/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Integer.
 */

#include <limits>
#include <sstream>

#include "base/exception.h"
#include "test.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackInteger : public TestInternal
{
 protected:
  uint32_t internalLength(int32_t i)
  {
    if (i == 0)
    {
      return 1;
    }
    else
    {
      int32_t absi = i < 0 ? -i : i;
      uint32_t n = 0;
      int32_t powN = 1;
      do
      {
        powN <<= 1;
        ++n;
      } while (absi >= powN);
      return n;
    }
  }
  static const char* s_large_val;
  static const char* s_lots_of_leading_zeros;
};

const char* TestUtilBlackInteger::s_large_val =
    "4547897890548754897897897897890789078907890";
const char* TestUtilBlackInteger::s_lots_of_leading_zeros =
    "00000000000000000000000000000000000000000000000000000000000000000000000000"
    "000000000000000000000000000000000000000000000000000000000000000000000001";

TEST_F(TestUtilBlackInteger, constructors)
{
  Integer z0(1);
  ASSERT_EQ(z0.getLong(), 1);

  Integer z1(0);
  ASSERT_EQ(z1.getLong(), 0);

  Integer z2(-1);
  ASSERT_EQ(z2.getLong(), -1);

  Integer z3(0x890UL);
  ASSERT_EQ(z3.getUnsignedLong(), 0x890UL);

  Integer z4;
  ASSERT_EQ(z4.getLong(), 0);

  Integer z5("7896890");
  ASSERT_EQ(z5.getUnsignedLong(), 7896890ul);

  Integer z6(z5);
  ASSERT_EQ(z5.getUnsignedLong(), 7896890ul);
  ASSERT_EQ(z6.getUnsignedLong(), 7896890ul);

  std::string bigValue("1536729");
  Integer z7(bigValue);
  ASSERT_EQ(z7.getUnsignedLong(), 1536729ul);
}

TEST_F(TestUtilBlackInteger, compare_against_zero)
{
  Integer z(0);
  ASSERT_NO_THROW((void)(z == 0););
  ASSERT_EQ(z, 0);
}

TEST_F(TestUtilBlackInteger, operator_assign)
{
  Integer x(0);
  Integer y(79);
  Integer z(45789);

  ASSERT_EQ(x.getUnsignedLong(), 0ul);
  ASSERT_EQ(y.getUnsignedLong(), 79ul);
  ASSERT_EQ(z.getUnsignedLong(), 45789ul);

  x = y = z;

  ASSERT_EQ(x.getUnsignedLong(), 45789ul);
  ASSERT_EQ(y.getUnsignedLong(), 45789ul);
  ASSERT_EQ(z.getUnsignedLong(), 45789ul);

  Integer a(2);

  y = a;

  ASSERT_EQ(a.getUnsignedLong(), 2ul);
  ASSERT_EQ(y.getUnsignedLong(), 2ul);
  ASSERT_EQ(x.getUnsignedLong(), 45789ul);
  ASSERT_EQ(z.getUnsignedLong(), 45789ul);
}

TEST_F(TestUtilBlackInteger, operator_equals)
{
  Integer a(0);
  Integer b(79);
  Integer c("79");
  Integer d;

  ASSERT_TRUE(a == a);
  ASSERT_FALSE(a == b);
  ASSERT_FALSE(a == c);
  ASSERT_TRUE(a == d);

  ASSERT_FALSE(b == a);
  ASSERT_TRUE(b == b);
  ASSERT_TRUE(b == c);
  ASSERT_FALSE(b == d);

  ASSERT_FALSE(c == a);
  ASSERT_TRUE(c == b);
  ASSERT_TRUE(c == c);
  ASSERT_FALSE(c == d);

  ASSERT_TRUE(d == a);
  ASSERT_FALSE(d == b);
  ASSERT_FALSE(d == c);
  ASSERT_TRUE(d == d);
}

TEST_F(TestUtilBlackInteger, operator_not_equals)
{
  Integer a(0);
  Integer b(79);
  Integer c("79");
  Integer d;

  ASSERT_FALSE(a != a);
  ASSERT_TRUE(a != b);
  ASSERT_TRUE(a != c);
  ASSERT_FALSE(a != d);

  ASSERT_TRUE(b != a);
  ASSERT_FALSE(b != b);
  ASSERT_FALSE(b != c);
  ASSERT_TRUE(b != d);

  ASSERT_TRUE(c != a);
  ASSERT_FALSE(c != b);
  ASSERT_FALSE(c != c);
  ASSERT_TRUE(c != d);

  ASSERT_FALSE(d != a);
  ASSERT_TRUE(d != b);
  ASSERT_TRUE(d != c);
  ASSERT_FALSE(d != d);
}

TEST_F(TestUtilBlackInteger, operator_subtract)
{
  Integer x(0);
  Integer y(79);
  Integer z(-34);

  Integer act0 = x - x;
  Integer act1 = x - y;
  Integer act2 = x - z;
  Integer exp0(0);
  Integer exp1(-79);
  Integer exp2(34);

  Integer act3 = y - x;
  Integer act4 = y - y;
  Integer act5 = y - z;
  Integer exp3(79);
  Integer exp4(0);
  Integer exp5(113);

  Integer act6 = z - x;
  Integer act7 = z - y;
  Integer act8 = z - z;
  Integer exp6(-34);
  Integer exp7(-113);
  Integer exp8(0);

  ASSERT_EQ(act0, exp0);
  ASSERT_EQ(act1, exp1);
  ASSERT_EQ(act2, exp2);
  ASSERT_EQ(act3, exp3);
  ASSERT_EQ(act4, exp4);
  ASSERT_EQ(act5, exp5);
  ASSERT_EQ(act6, exp6);
  ASSERT_EQ(act7, exp7);
  ASSERT_EQ(act8, exp8);
}

TEST_F(TestUtilBlackInteger, operator_add)
{
  Integer x(0);
  Integer y(79);
  Integer z(-34);

  Integer act0 = x + x;
  Integer act1 = x + y;
  Integer act2 = x + z;
  Integer exp0(0);
  Integer exp1(79);
  Integer exp2(-34);

  Integer act3 = y + x;
  Integer act4 = y + y;
  Integer act5 = y + z;
  Integer exp3(79);
  Integer exp4(158);
  Integer exp5(45);

  Integer act6 = z + x;
  Integer act7 = z + y;
  Integer act8 = z + z;
  Integer exp6(-34);
  Integer exp7(45);
  Integer exp8(-68);

  ASSERT_EQ(act0, exp0);
  ASSERT_EQ(act1, exp1);
  ASSERT_EQ(act2, exp2);
  ASSERT_EQ(act3, exp3);
  ASSERT_EQ(act4, exp4);
  ASSERT_EQ(act5, exp5);
  ASSERT_EQ(act6, exp6);
  ASSERT_EQ(act7, exp7);
  ASSERT_EQ(act8, exp8);
}

TEST_F(TestUtilBlackInteger, operator_mult)
{
  Integer x(0);
  Integer y(79);
  Integer z(-34);

  Integer act0 = x * x;
  Integer act1 = x * y;
  Integer act2 = x * z;
  Integer exp0(0);
  Integer exp1(0);
  Integer exp2(0);

  Integer act3 = y * x;
  Integer act4 = y * y;
  Integer act5 = y * z;
  Integer exp3(0);
  Integer exp4(6241);
  Integer exp5(-2686);

  Integer act6 = z * x;
  Integer act7 = z * y;
  Integer act8 = z * z;
  Integer exp6(0);
  Integer exp7(-2686);
  Integer exp8(1156);

  ASSERT_EQ(act0, exp0);
  ASSERT_EQ(act1, exp1);
  ASSERT_EQ(act2, exp2);
  ASSERT_EQ(act3, exp3);
  ASSERT_EQ(act4, exp4);
  ASSERT_EQ(act5, exp5);
  ASSERT_EQ(act6, exp6);
  ASSERT_EQ(act7, exp7);
  ASSERT_EQ(act8, exp8);
}

TEST_F(TestUtilBlackInteger, to_string)
{
  std::stringstream ss;
  Integer large(s_large_val);
  ss << large;
  std::string res = ss.str();

  ASSERT_EQ(res, large.toString());
}

TEST_F(TestUtilBlackInteger, base_inference)
{
  ASSERT_EQ(Integer("0xa", 0), 10);
  ASSERT_EQ(Integer("0xff", 0), 255);
  ASSERT_EQ(Integer("011", 0), 9);
  ASSERT_EQ(Integer("0b1010", 0), 10);
  ASSERT_EQ(Integer("-1", 0), -1);
  ASSERT_EQ(Integer("42", 0), 42);
}

TEST_F(TestUtilBlackInteger, parse_errors)
{
  ASSERT_THROW(Integer("abracadabra"), std::invalid_argument);
  ASSERT_THROW(Integer("+-1"), std::invalid_argument);
  ASSERT_THROW(Integer("-+1"), std::invalid_argument);
  ASSERT_THROW(Integer("5i"), std::invalid_argument);
  ASSERT_THROW(Integer("10xyz"), std::invalid_argument);
  ASSERT_THROW(Integer("0xff", 10), std::invalid_argument);
  ASSERT_THROW(Integer("#x5", 0), std::invalid_argument);
  ASSERT_THROW(Integer("0b123", 0), std::invalid_argument);
}

TEST_F(TestUtilBlackInteger, pow)
{
  ASSERT_EQ(Integer(1), Integer(1).pow(0));
  ASSERT_EQ(Integer(1), Integer(5).pow(0));
  ASSERT_EQ(Integer(1), Integer(-1).pow(0));
  ASSERT_EQ(Integer(0), Integer(0).pow(1));
  ASSERT_EQ(Integer(5), Integer(5).pow(1));
  ASSERT_EQ(Integer(-5), Integer(-5).pow(1));
  ASSERT_EQ(Integer(16), Integer(2).pow(4));
  ASSERT_EQ(Integer(16), Integer(-2).pow(4));
  ASSERT_EQ(Integer(1000), Integer(10).pow(3));
  ASSERT_EQ(Integer(-1000), Integer(-10).pow(3));
}

TEST_F(TestUtilBlackInteger, overly_long_signed)
{
  int64_t sl = std::numeric_limits<int64_t>::max();
  Integer i(sl);
  if constexpr (sizeof(unsigned long) == sizeof(uint64_t))
  {
    ASSERT_EQ(i.getLong(), sl);
  }
  ASSERT_NO_THROW(i.getSigned64());
  ASSERT_EQ(i.getSigned64(), sl);
  i = i + 1;
  ASSERT_DEATH(i.getSigned64(), "Overflow detected");
}

TEST_F(TestUtilBlackInteger, overly_long_unsigned)
{
  uint64_t ul = std::numeric_limits<uint64_t>::max();
  Integer i(ul);
  if constexpr (sizeof(unsigned long) == sizeof(uint64_t))
  {
    ASSERT_EQ(i.getUnsignedLong(), ul);
  }
  ASSERT_DEATH(i.getLong(), "Overflow detected");
  ASSERT_NO_THROW(i.getUnsigned64());
  ASSERT_EQ(i.getUnsigned64(), ul);
  uint64_t ulplus1 = ul + 1;
  ASSERT_EQ(ulplus1, 0);
  i = i + 1;
  ASSERT_DEATH(i.getUnsignedLong(), "Overflow detected");
}

TEST_F(TestUtilBlackInteger, getSigned64)
{
  {
    int64_t i = std::numeric_limits<int64_t>::max();
    Integer a(i);
    ASSERT_EQ(a.getSigned64(), i);
    ASSERT_DEATH((a + 1).getSigned64(), "Overflow detected");
  }
  {
    int64_t i = std::numeric_limits<int64_t>::min();
    Integer a(i);
    ASSERT_EQ(a.getSigned64(), i);
    ASSERT_DEATH((a - 1).getSigned64(), "Overflow detected");
  }
}

TEST_F(TestUtilBlackInteger, getUnsigned64)
{
  {
    uint64_t i = std::numeric_limits<uint64_t>::max();
    Integer a(i);
    ASSERT_EQ(a.getUnsigned64(), i);
    ASSERT_DEATH((a + 1).getUnsigned64(), "Overflow detected");
  }
  {
    uint64_t i = std::numeric_limits<uint64_t>::min();
    Integer a(i);
    ASSERT_EQ(a.getUnsigned64(), i);
    ASSERT_DEATH((a - 1).getUnsigned64(), "Overflow detected");
  }
}

TEST_F(TestUtilBlackInteger, testBit)
{
  ASSERT_FALSE(Integer(0).testBit(6));
  ASSERT_FALSE(Integer(0).testBit(5));
  ASSERT_FALSE(Integer(0).testBit(4));
  ASSERT_FALSE(Integer(0).testBit(3));
  ASSERT_FALSE(Integer(0).testBit(2));
  ASSERT_FALSE(Integer(0).testBit(1));
  ASSERT_FALSE(Integer(0).testBit(0));

  ASSERT_TRUE(Integer(-1).testBit(6));
  ASSERT_TRUE(Integer(-1).testBit(5));
  ASSERT_TRUE(Integer(-1).testBit(4));
  ASSERT_TRUE(Integer(-1).testBit(3));
  ASSERT_TRUE(Integer(-1).testBit(2));
  ASSERT_TRUE(Integer(-1).testBit(1));
  ASSERT_TRUE(Integer(-1).testBit(0));

  ASSERT_FALSE(Integer(10).testBit(6));
  ASSERT_FALSE(Integer(10).testBit(5));
  ASSERT_FALSE(Integer(10).testBit(4));
  ASSERT_TRUE(Integer(10).testBit(3));
  ASSERT_FALSE(Integer(10).testBit(2));
  ASSERT_TRUE(Integer(10).testBit(1));
  ASSERT_FALSE(Integer(10).testBit(0));

  ASSERT_FALSE(Integer(14).testBit(6));
  ASSERT_FALSE(Integer(14).testBit(5));
  ASSERT_FALSE(Integer(14).testBit(4));
  ASSERT_TRUE(Integer(14).testBit(3));
  ASSERT_TRUE(Integer(14).testBit(2));
  ASSERT_TRUE(Integer(14).testBit(1));
  ASSERT_FALSE(Integer(14).testBit(0));

  ASSERT_TRUE(Integer(64).testBit(6));
  ASSERT_FALSE(Integer(64).testBit(5));
  ASSERT_FALSE(Integer(64).testBit(4));
  ASSERT_FALSE(Integer(64).testBit(3));
  ASSERT_FALSE(Integer(64).testBit(2));
  ASSERT_FALSE(Integer(64).testBit(1));
  ASSERT_FALSE(Integer(64).testBit(0));
}

TEST_F(TestUtilBlackInteger, length)
{
  for (int32_t i = -17; i <= 17; ++i)
  {
    ASSERT_EQ(Integer(i).length(), internalLength(i));
  }
}

TEST_F(TestUtilBlackInteger, euclidianQR)
{
  Integer q, r;

  Integer::euclidianQR(q, r, 1, 4);
  ASSERT_EQ(q, Integer(0));
  ASSERT_EQ(r, Integer(1));

  Integer::euclidianQR(q, r, 1, -4);
  ASSERT_EQ(q, Integer(0));
  ASSERT_EQ(r, Integer(1));

  Integer::euclidianQR(q, r, -1, 4);
  ASSERT_EQ(q, Integer(-1));
  ASSERT_EQ(r, Integer(3));

  Integer::euclidianQR(q, r, -1, -4);
  ASSERT_EQ(q, Integer(1));
  ASSERT_EQ(r, Integer(3));

  Integer::euclidianQR(q, r, 5, 4);
  ASSERT_EQ(q, Integer(1));
  ASSERT_EQ(r, Integer(1));

  Integer::euclidianQR(q, r, 5, -4);
  ASSERT_EQ(q, Integer(-1));
  ASSERT_EQ(r, Integer(1));

  Integer::euclidianQR(q, r, -5, 4);
  ASSERT_EQ(q, Integer(-2));
  ASSERT_EQ(r, Integer(3));

  Integer::euclidianQR(q, r, -5, -4);
  ASSERT_EQ(q, Integer(2));
  ASSERT_EQ(r, Integer(3));
}

TEST_F(TestUtilBlackInteger, floorQR)
{
  Integer q, r;

  Integer::floorQR(q, r, 1, 4);
  ASSERT_EQ(q, Integer(0));
  ASSERT_EQ(r, Integer(1));

  Integer::floorQR(q, r, 1, -4);
  ASSERT_EQ(q, Integer(-1));
  ASSERT_EQ(r, Integer(-3));

  Integer::floorQR(q, r, -1, 4);
  ASSERT_EQ(q, Integer(-1));
  ASSERT_EQ(r, Integer(3));

  Integer::floorQR(q, r, -1, -4);
  ASSERT_EQ(q, Integer(0));
  ASSERT_EQ(r, Integer(-1));

  Integer::floorQR(q, r, 5, 4);
  ASSERT_EQ(q, Integer(1));
  ASSERT_EQ(r, Integer(1));

  Integer::floorQR(q, r, 5, -4);
  ASSERT_EQ(q, Integer(-2));
  ASSERT_EQ(r, Integer(-3));

  Integer::floorQR(q, r, -5, 4);
  ASSERT_EQ(q, Integer(-2));
  ASSERT_EQ(r, Integer(3));

  Integer::floorQR(q, r, -5, -4);
  ASSERT_EQ(q, Integer(1));
  ASSERT_EQ(r, Integer(-1));
}

TEST_F(TestUtilBlackInteger, leadingZeros)
{
  std::string leadingZeros(s_lots_of_leading_zeros);
  Integer one(1u);
  Integer one_from_string(leadingZeros, 2);
  ASSERT_EQ(one, one_from_string);
}

TEST_F(TestUtilBlackInteger, modAdd)
{
  for (uint32_t i = 0; i <= 10; ++i)
  {
    for (uint32_t j = 0; j <= 10; ++j)
    {
      Integer yy;
      Integer x(i);
      Integer y = x + j;
      Integer yp = x.modAdd(j, 3);
      for (yy = y; yy >= 3; yy -= 3)
        ;
      ASSERT_EQ(yp, yy);
      yp = x.modAdd(j, 7);
      for (yy = y; yy >= 7; yy -= 7)
        ;
      ASSERT_EQ(yp, yy);
      yp = x.modAdd(j, 11);
      for (yy = y; yy >= 11; yy -= 11)
        ;
      ASSERT_EQ(yp, yy);
    }
  }
}

TEST_F(TestUtilBlackInteger, modMultiply)
{
  for (uint32_t i = 0; i <= 10; ++i)
  {
    for (uint32_t j = 0; j <= 10; ++j)
    {
      Integer yy;
      Integer x(i);
      Integer y = x * j;
      Integer yp = x.modMultiply(j, 3);
      for (yy = y; yy >= 3; yy -= 3)
        ;
      ASSERT_EQ(yp, yy);
      yp = x.modMultiply(j, 7);
      for (yy = y; yy >= 7; yy -= 7)
        ;
      ASSERT_EQ(yp, yy);
      yp = x.modMultiply(j, 11);
      for (yy = y; yy >= 11; yy -= 11)
        ;
      ASSERT_EQ(yp, yy);
    }
  }
}

TEST_F(TestUtilBlackInteger, modInverse)
{
  for (uint32_t i = 0; i <= 10; ++i)
  {
    Integer x(i);
    Integer inv = x.modInverse(3);
    if (i == 0 || i == 3 || i == 6 || i == 9)
    {
      ASSERT_EQ(inv, -1); /* no inverse */
    }
    else
    {
      ASSERT_EQ(x.modMultiply(inv, 3), 1);
    }
    inv = x.modInverse(7);
    if (i == 0 || i == 7)
    {
      ASSERT_EQ(inv, -1); /* no inverse */
    }
    else
    {
      ASSERT_EQ(x.modMultiply(inv, 7), 1);
    }
    inv = x.modInverse(11);
    if (i == 0)
    {
      ASSERT_EQ(inv, -1); /* no inverse */
    }
    else
    {
      ASSERT_EQ(x.modMultiply(inv, 11), 1);
    }
  }
}
}  // namespace test
}  // namespace cvc5::internal
