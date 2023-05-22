/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::Rational.
 */

#include <sstream>

#include "test.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestUtilWhiteRational : public TestInternal
{
 protected:
  static const char* s_can_reduce;
};

const char* TestUtilWhiteRational::s_can_reduce =
    "4547897890548754897897897897890789078907890/54878902347890234";

TEST_F(TestUtilWhiteRational, constructors)
{
  Rational zero;  // Default constructor
  ASSERT_EQ(0L, zero.getNumerator().getLong());
  ASSERT_EQ(1L, zero.getDenominator().getLong());

  Rational reduced_cstring_base_10(s_can_reduce);
  Integer tmp0("2273948945274377448948948948945394539453945");
  Integer tmp1("27439451173945117");
  ASSERT_EQ(reduced_cstring_base_10.getNumerator(), tmp0);
  ASSERT_EQ(reduced_cstring_base_10.getDenominator(), tmp1);

  Rational reduced_cstring_base_16(s_can_reduce, 16);
  Integer tmp2("405008068100961292527303019616635131091442462891556", 10);
  Integer tmp3("24363950654420566157", 10);
  ASSERT_EQ(tmp2, reduced_cstring_base_16.getNumerator());
  ASSERT_EQ(tmp3, reduced_cstring_base_16.getDenominator());

  std::string stringCanReduce(s_can_reduce);
  Rational reduced_cppstring_base_10(stringCanReduce);
  ASSERT_EQ(reduced_cppstring_base_10.getNumerator(), tmp0);
  ASSERT_EQ(reduced_cppstring_base_10.getDenominator(), tmp1);
  Rational reduced_cppstring_base_16(stringCanReduce, 16);
  ASSERT_EQ(tmp2, reduced_cppstring_base_16.getNumerator());
  ASSERT_EQ(tmp3, reduced_cppstring_base_16.getDenominator());

  Rational cpy_cnstr(zero);
  ASSERT_EQ(0L, cpy_cnstr.getNumerator().getLong());
  ASSERT_EQ(1L, cpy_cnstr.getDenominator().getLong());
  // Check that zero is unaffected
  ASSERT_EQ(0L, zero.getNumerator().getLong());
  ASSERT_EQ(1L, zero.getDenominator().getLong());

  signed int nsi = -5478, dsi = 34783;
  unsigned int nui = 5478u, dui = 347589u;
  signed long int nsli = 1489054690l, dsli = -347576678l;
  unsigned long int nuli = 2434689476ul, duli = 323447523ul;

  Rational qsi(nsi, dsi);
  Rational qui(nui, dui);
  Rational qsli(nsli, dsli);
  Rational quli(nuli, duli);

  ASSERT_EQ(nsi, qsi.getNumerator().getLong());
  ASSERT_EQ(dsi, qsi.getDenominator().getLong());

  ASSERT_EQ(nui / 33, qui.getNumerator().getUnsignedLong());
  ASSERT_EQ(dui / 33, qui.getDenominator().getUnsignedLong());

  ASSERT_EQ(-nsli / 2, qsli.getNumerator().getLong());
  ASSERT_EQ(-dsli / 2, qsli.getDenominator().getLong());

  ASSERT_EQ(nuli, quli.getNumerator().getUnsignedLong());
  ASSERT_EQ(duli, quli.getDenominator().getUnsignedLong());

  Integer nz("942358903458908903485");
  Integer dz("547890579034790793457934807");
  Rational qz(nz, dz);
  ASSERT_EQ(nz, qz.getNumerator());
  ASSERT_EQ(dz, qz.getDenominator());

  // Not sure how to catch this...
  // ASSERT_THROW(Rational div_0(0,0),__gmp_exception );
}

TEST_F(TestUtilWhiteRational, destructor)
{
  Rational* q = new Rational(s_can_reduce);
  ASSERT_NO_THROW(delete q);
}

TEST_F(TestUtilWhiteRational, compare_against_zero)
{
  Rational q(0);
  ASSERT_NO_THROW(q == 0;);
  ASSERT_EQ(q, 0);
}

TEST_F(TestUtilWhiteRational, operator_assign)
{
  Rational x(0, 1);
  Rational y(78, 6);
  Rational z(45789, 1);

  ASSERT_EQ(x.getNumerator().getUnsignedLong(), 0ul);
  ASSERT_EQ(y.getNumerator().getUnsignedLong(), 13ul);
  ASSERT_EQ(z.getNumerator().getUnsignedLong(), 45789ul);

  x = y = z;

  ASSERT_EQ(x.getNumerator().getUnsignedLong(), 45789ul);
  ASSERT_EQ(y.getNumerator().getUnsignedLong(), 45789ul);
  ASSERT_EQ(z.getNumerator().getUnsignedLong(), 45789ul);

  Rational a(78, 91);

  y = a;

  ASSERT_EQ(a.getNumerator().getUnsignedLong(), 6ul);
  ASSERT_EQ(a.getDenominator().getUnsignedLong(), 7ul);
  ASSERT_EQ(y.getNumerator().getUnsignedLong(), 6ul);
  ASSERT_EQ(y.getDenominator().getUnsignedLong(), 7ul);
  ASSERT_EQ(x.getNumerator().getUnsignedLong(), 45789ul);
  ASSERT_EQ(z.getNumerator().getUnsignedLong(), 45789ul);
}

TEST_F(TestUtilWhiteRational, toString)
{
  std::stringstream ss;
  Rational large(s_can_reduce);
  ss << large;
  std::string res = ss.str();

  ASSERT_EQ(res, large.toString());
}

TEST_F(TestUtilWhiteRational, operator_equals)
{
  Rational a;
  Rational b(s_can_reduce);
  Rational c("2273948945274377448948948948945394539453945/27439451173945117");
  Rational d(0, -237489);

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

TEST_F(TestUtilWhiteRational, operator_not_equals)
{
  Rational a;
  Rational b(s_can_reduce);
  Rational c("2273948945274377448948948948945394539453945/27439451173945117");
  Rational d(0, -237489);

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

TEST_F(TestUtilWhiteRational, operator_subtract)
{
  Rational x(3, 2);
  Rational y(7, 8);
  Rational z(-3, 33);

  Rational act0 = x - x;
  Rational act1 = x - y;
  Rational act2 = x - z;
  Rational exp0(0, 1);
  Rational exp1(5, 8);
  Rational exp2(35, 22);

  Rational act3 = y - x;
  Rational act4 = y - y;
  Rational act5 = y - z;
  Rational exp3(-5, 8);
  Rational exp4(0, 1);
  Rational exp5(85, 88);

  Rational act6 = z - x;
  Rational act7 = z - y;
  Rational act8 = z - z;
  Rational exp6(-35, 22);
  Rational exp7(-85, 88);
  Rational exp8(0, 1);

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

TEST_F(TestUtilWhiteRational, operator_add)
{
  Rational x(3, 2);
  Rational y(7, 8);
  Rational z(-3, 33);

  Rational act0 = x + x;
  Rational act1 = x + y;
  Rational act2 = x + z;
  Rational exp0(3, 1);
  Rational exp1(19, 8);
  Rational exp2(31, 22);

  Rational act3 = y + x;
  Rational act4 = y + y;
  Rational act5 = y + z;
  Rational exp3(19, 8);
  Rational exp4(7, 4);
  Rational exp5(69, 88);

  Rational act6 = z + x;
  Rational act7 = z + y;
  Rational act8 = z + z;
  Rational exp6(31, 22);
  Rational exp7(69, 88);
  Rational exp8(-2, 11);

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

TEST_F(TestUtilWhiteRational, operator_mult)
{
  Rational x(3, 2);
  Rational y(7, 8);
  Rational z(-3, 33);

  Rational act0 = x * x;
  Rational act1 = x * y;
  Rational act2 = x * z;
  Rational exp0(9, 4);
  Rational exp1(21, 16);
  Rational exp2(-3, 22);

  Rational act3 = y * x;
  Rational act4 = y * y;
  Rational act5 = y * z;
  Rational exp3(21, 16);
  Rational exp4(49, 64);
  Rational exp5(-7, 88);

  Rational act6 = z * x;
  Rational act7 = z * y;
  Rational act8 = z * z;
  Rational exp6(-3, 22);
  Rational exp7(-7, 88);
  Rational exp8(1, 121);

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

TEST_F(TestUtilWhiteRational, operator_div)
{
  Rational x(3, 2);
  Rational y(7, 8);
  Rational z(-3, 33);

  Rational act0 = x / x;
  Rational act1 = x / y;
  Rational act2 = x / z;
  Rational exp0(1, 1);
  Rational exp1(12, 7);
  Rational exp2(-33, 2);

  Rational act3 = y / x;
  Rational act4 = y / y;
  Rational act5 = y / z;
  Rational exp3(7, 12);
  Rational exp4(1, 1);
  Rational exp5(-77, 8);

  Rational act6 = z / x;
  Rational act7 = z / y;
  Rational act8 = z / z;
  Rational exp6(-2, 33);
  Rational exp7(-8, 77);
  Rational exp8(1, 1);

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

TEST_F(TestUtilWhiteRational, reduction_at_construction_time)
{
  Rational reduce0(s_can_reduce);
  Integer num0("2273948945274377448948948948945394539453945");
  Integer den0("27439451173945117");

  ASSERT_EQ(reduce0.getNumerator(), num0);
  ASSERT_EQ(reduce0.getDenominator(), den0);

  Rational reduce1(0, 454789);
  Integer num1(0);
  Integer den1(1);

  ASSERT_EQ(reduce1.getNumerator(), num1);
  ASSERT_EQ(reduce1.getDenominator(), den1);

  Rational reduce2(0, -454789);
  Integer num2(0);
  Integer den2(1);

  ASSERT_EQ(reduce2.getNumerator(), num2);
  ASSERT_EQ(reduce2.getDenominator(), den2);

  Rational reduce3(822898902L, 273L);
  Integer num3(39185662L);
  Integer den3(13);

  ASSERT_EQ(reduce2.getNumerator(), num2);
  ASSERT_EQ(reduce2.getDenominator(), den2);

  Rational reduce4(822898902L, -273L);
  Integer num4(-39185662L);
  Integer den4(13);

  ASSERT_EQ(reduce4.getNumerator(), num4);
  ASSERT_EQ(reduce4.getDenominator(), den4);

  Rational reduce5(-822898902L, 273L);
  Integer num5(-39185662L);
  Integer den5(13);

  ASSERT_EQ(reduce5.getNumerator(), num5);
  ASSERT_EQ(reduce5.getDenominator(), den5);

  Rational reduce6(-822898902L, -273L);
  Integer num6(39185662L);
  Integer den6(13);

  ASSERT_EQ(reduce6.getNumerator(), num6);
  ASSERT_EQ(reduce6.getDenominator(), den6);
}

/** Make sure we can handle: http://www.ginac.de/CLN/cln_3.html#SEC15 */
TEST_F(TestUtilWhiteRational, constructrion)
{
  const int32_t i = (1 << 29) + 1;
  const uint32_t u = (1 << 29) + 1;
  ASSERT_EQ(Rational(i), Rational(i));
  ASSERT_EQ(Rational(u), Rational(u));
}
}  // namespace test
}  // namespace cvc5::internal
