/*********************                                                        */
/*! \file rational_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::Rational.
 **
 ** White box testing of CVC4::Rational.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/rational.h"

using namespace CVC4;
using namespace std;

const char* canReduce = "4547897890548754897897897897890789078907890/54878902347890234";

class RationalWhite : public CxxTest::TestSuite {
public:


  void testDestructor(){
    Rational* q = new Rational(canReduce);
    TS_ASSERT_THROWS_NOTHING( delete q );
  }

  void testCompareAgainstZero(){
    Rational q(0);
    TS_ASSERT_THROWS_NOTHING(q == 0;);
    TS_ASSERT_EQUALS(q,0);
  }

  void testConstructors(){
    Rational zero; //Default constructor
    TS_ASSERT_EQUALS(0L, zero.getNumerator().getLong());
    TS_ASSERT_EQUALS(1L, zero.getDenominator().getLong());

    Rational reduced_cstring_base_10(canReduce);
    Integer tmp0("2273948945274377448948948948945394539453945");
    Integer tmp1("27439451173945117");
    TS_ASSERT_EQUALS(reduced_cstring_base_10.getNumerator(), tmp0);
    TS_ASSERT_EQUALS(reduced_cstring_base_10.getDenominator(), tmp1);

    Rational reduced_cstring_base_16(canReduce, 16);
    Integer tmp2("405008068100961292527303019616635131091442462891556",10);
    Integer tmp3("24363950654420566157",10);
    TS_ASSERT_EQUALS(tmp2, reduced_cstring_base_16.getNumerator());
    TS_ASSERT_EQUALS(tmp3, reduced_cstring_base_16.getDenominator());

    string stringCanReduce(canReduce);
    Rational reduced_cppstring_base_10(stringCanReduce);
    TS_ASSERT_EQUALS(reduced_cppstring_base_10.getNumerator(), tmp0);
    TS_ASSERT_EQUALS(reduced_cppstring_base_10.getDenominator(), tmp1);
    Rational reduced_cppstring_base_16(stringCanReduce, 16);
    TS_ASSERT_EQUALS(tmp2, reduced_cppstring_base_16.getNumerator());
    TS_ASSERT_EQUALS(tmp3, reduced_cppstring_base_16.getDenominator());

    Rational cpy_cnstr(zero);
    TS_ASSERT_EQUALS(0L, cpy_cnstr.getNumerator().getLong());
    TS_ASSERT_EQUALS(1L, cpy_cnstr.getDenominator().getLong());
    //Check that zero is unaffected
    TS_ASSERT_EQUALS(0L, zero.getNumerator().getLong());
    TS_ASSERT_EQUALS(1L, zero.getDenominator().getLong());


    signed int nsi = -5478, dsi = 34783;
    unsigned int nui = 5478u, dui = 347589u;
    signed long int nsli = 1489054690l, dsli = -347576678l;
    unsigned long int nuli = 2434689476ul, duli = 323447523ul;

    Rational qsi(nsi, dsi);
    Rational qui(nui, dui);
    Rational qsli(nsli, dsli);
    Rational quli(nuli, duli);

    TS_ASSERT_EQUALS(nsi, qsi.getNumerator().getLong());
    TS_ASSERT_EQUALS(dsi, qsi.getDenominator().getLong());


    TS_ASSERT_EQUALS(nui/33, qui.getNumerator().getUnsignedLong());
    TS_ASSERT_EQUALS(dui/33, qui.getDenominator().getUnsignedLong());


    TS_ASSERT_EQUALS(-nsli/2, qsli.getNumerator().getLong());
    TS_ASSERT_EQUALS(-dsli/2, qsli.getDenominator().getLong());

    TS_ASSERT_EQUALS(nuli, quli.getNumerator().getUnsignedLong());
    TS_ASSERT_EQUALS(duli, quli.getDenominator().getUnsignedLong());

    Integer nz("942358903458908903485");
    Integer dz("547890579034790793457934807");
    Rational qz(nz, dz);
    TS_ASSERT_EQUALS(nz, qz.getNumerator());
    TS_ASSERT_EQUALS(dz, qz.getDenominator());

    //Not sure how to catch this...
    //TS_ASSERT_THROWS(Rational div_0(0,0),__gmp_exception );
  }

  void testOperatorAssign(){
    Rational x(0,1);
    Rational y(78,6);
    Rational z(45789,1);

    TS_ASSERT_EQUALS(x.getNumerator().getUnsignedLong(), 0ul);
    TS_ASSERT_EQUALS(y.getNumerator().getUnsignedLong(), 13ul);
    TS_ASSERT_EQUALS(z.getNumerator().getUnsignedLong(), 45789ul);

    x = y = z;

    TS_ASSERT_EQUALS(x.getNumerator().getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(y.getNumerator().getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(z.getNumerator().getUnsignedLong(), 45789ul);

    Rational a(78,91);

    y = a;

    TS_ASSERT_EQUALS(a.getNumerator().getUnsignedLong(), 6ul);
    TS_ASSERT_EQUALS(a.getDenominator().getUnsignedLong(), 7ul);
    TS_ASSERT_EQUALS(y.getNumerator().getUnsignedLong(), 6ul);
    TS_ASSERT_EQUALS(y.getDenominator().getUnsignedLong(), 7ul);
    TS_ASSERT_EQUALS(x.getNumerator().getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(z.getNumerator().getUnsignedLong(), 45789ul);
  }

  void testToStringStuff(){
    stringstream ss;
    Rational large (canReduce);
    ss << large;
    string res = ss.str();

    TS_ASSERT_EQUALS(res, large.toString());
  }
  void testOperatorEquals(){
    Rational a;
    Rational b(canReduce);
    Rational c("2273948945274377448948948948945394539453945/27439451173945117");
    Rational d(0,-237489);

    TS_ASSERT( (a==a));
    TS_ASSERT(!(a==b));
    TS_ASSERT(!(a==c));
    TS_ASSERT( (a==d));

    TS_ASSERT(!(b==a));
    TS_ASSERT( (b==b));
    TS_ASSERT( (b==c));
    TS_ASSERT(!(b==d));

    TS_ASSERT(!(c==a));
    TS_ASSERT( (c==b));
    TS_ASSERT( (c==c));
    TS_ASSERT(!(c==d));

    TS_ASSERT( (d==a));
    TS_ASSERT(!(d==b));
    TS_ASSERT(!(d==c));
    TS_ASSERT( (d==d));

  }
  void testOperatorNotEquals(){
    Rational a;
    Rational b(canReduce);
    Rational c("2273948945274377448948948948945394539453945/27439451173945117");
    Rational d(0,-237489);

    TS_ASSERT(!(a!=a));
    TS_ASSERT( (a!=b));
    TS_ASSERT( (a!=c));
    TS_ASSERT(!(a!=d));

    TS_ASSERT( (b!=a));
    TS_ASSERT(!(b!=b));
    TS_ASSERT(!(b!=c));
    TS_ASSERT( (b!=d));

    TS_ASSERT( (c!=a));
    TS_ASSERT(!(c!=b));
    TS_ASSERT(!(c!=c));
    TS_ASSERT( (c!=d));

    TS_ASSERT(!(d!=a));
    TS_ASSERT( (d!=b));
    TS_ASSERT( (d!=c));
    TS_ASSERT(!(d!=d));

  }
  void testOperatorSubtract(){
    Rational x(3,2);
    Rational y(7,8);
    Rational z(-3,33);


    Rational act0 = x - x;
    Rational act1 = x - y;
    Rational act2 = x - z;
    Rational exp0(0,1);
    Rational exp1(5,8);
    Rational exp2(35,22);


    Rational act3 = y - x;
    Rational act4 = y - y;
    Rational act5 = y - z;
    Rational exp3(-5,8);
    Rational exp4(0,1);
    Rational exp5(85,88);


    Rational act6 = z - x;
    Rational act7 = z - y;
    Rational act8 = z - z;
    Rational exp6(-35,22);
    Rational exp7(-85, 88);
    Rational exp8(0, 1);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }
  void testOperatorAdd(){
    Rational x(3,2);
    Rational y(7,8);
    Rational z(-3,33);


    Rational act0 = x + x;
    Rational act1 = x + y;
    Rational act2 = x + z;
    Rational exp0(3,1);
    Rational exp1(19,8);
    Rational exp2(31,22);


    Rational act3 = y + x;
    Rational act4 = y + y;
    Rational act5 = y + z;
    Rational exp3(19,8);
    Rational exp4(7,4);
    Rational exp5(69,88);


    Rational act6 = z + x;
    Rational act7 = z + y;
    Rational act8 = z + z;
    Rational exp6(31,22);
    Rational exp7(69, 88);
    Rational exp8(-2, 11);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }

  void testOperatorMult(){
    Rational x(3,2);
    Rational y(7,8);
    Rational z(-3,33);


    Rational act0 = x * x;
    Rational act1 = x * y;
    Rational act2 = x * z;
    Rational exp0(9,4);
    Rational exp1(21,16);
    Rational exp2(-3,22);


    Rational act3 = y * x;
    Rational act4 = y * y;
    Rational act5 = y * z;
    Rational exp3(21,16);
    Rational exp4(49,64);
    Rational exp5(-7,88);


    Rational act6 = z * x;
    Rational act7 = z * y;
    Rational act8 = z * z;
    Rational exp6(-3, 22);
    Rational exp7(-7, 88);
    Rational exp8(1, 121);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }
  void testOperatorDiv(){
    Rational x(3,2);
    Rational y(7,8);
    Rational z(-3,33);


    Rational act0 = x / x;
    Rational act1 = x / y;
    Rational act2 = x / z;
    Rational exp0(1,1);
    Rational exp1(12,7);
    Rational exp2(-33,2);


    Rational act3 = y / x;
    Rational act4 = y / y;
    Rational act5 = y / z;
    Rational exp3(7,12);
    Rational exp4(1,1);
    Rational exp5(-77,8);


    Rational act6 = z / x;
    Rational act7 = z / y;
    Rational act8 = z / z;
    Rational exp6(-2,33);
    Rational exp7(-8, 77);
    Rational exp8(1, 1);



    TS_ASSERT_EQUALS(act0, exp0);
    TS_ASSERT_EQUALS(act1, exp1);
    TS_ASSERT_EQUALS(act2, exp2);
    TS_ASSERT_EQUALS(act3, exp3);
    TS_ASSERT_EQUALS(act4, exp4);
    TS_ASSERT_EQUALS(act5, exp5);
    TS_ASSERT_EQUALS(act6, exp6);
    TS_ASSERT_EQUALS(act7, exp7);
    TS_ASSERT_EQUALS(act8, exp8);
  }
  void testReductionAtConstructionTime(){
    Rational reduce0(canReduce);
    Integer num0("2273948945274377448948948948945394539453945");
    Integer den0("27439451173945117");

    TS_ASSERT_EQUALS(reduce0.getNumerator(), num0);
    TS_ASSERT_EQUALS(reduce0.getDenominator(), den0);

    Rational reduce1(0, 454789);
    Integer num1(0);
    Integer den1(1);

    TS_ASSERT_EQUALS(reduce1.getNumerator(), num1);
    TS_ASSERT_EQUALS(reduce1.getDenominator(), den1);

    Rational reduce2(0, -454789);
    Integer num2(0);
    Integer den2(1);


    TS_ASSERT_EQUALS(reduce2.getNumerator(), num2);
    TS_ASSERT_EQUALS(reduce2.getDenominator(), den2);


    Rational reduce3(822898902L, 273L);
    Integer num3(39185662L);
    Integer den3(13);

    TS_ASSERT_EQUALS(reduce2.getNumerator(), num2);
    TS_ASSERT_EQUALS(reduce2.getDenominator(), den2);

    Rational reduce4( 822898902L,-273L);
    Integer num4(-39185662L);
    Integer den4(13);


    TS_ASSERT_EQUALS(reduce4.getNumerator(), num4);
    TS_ASSERT_EQUALS(reduce4.getDenominator(), den4);

    Rational reduce5(-822898902L, 273L);
    Integer num5(-39185662L);
    Integer den5(13);


    TS_ASSERT_EQUALS(reduce5.getNumerator(), num5);
    TS_ASSERT_EQUALS(reduce5.getDenominator(), den5);

    Rational reduce6(-822898902L,-273L);
    Integer num6(39185662L);
    Integer den6(13);


    TS_ASSERT_EQUALS(reduce6.getNumerator(), num6);
    TS_ASSERT_EQUALS(reduce6.getDenominator(), den6);

  }

//   void testHash(){
//     Rational large (canReduce);
//     Rational zero;
//     Rational one_word(75890L,590L);
//     Rational two_words("7890D789D33234027890D789D3323402", 16);

//     TS_ASSERT_EQUALS(zero.hash(), 1u);
//     TS_ASSERT_EQUALS(one_word.hash(), 7589u xor 59u);
//     TS_ASSERT_EQUALS(two_words.hash(),
// 		     (two_words.getNumerator().hash()) xor 1);
//     TS_ASSERT_EQUALS(large.hash(),
//                      (large.getNumerator().hash()) xor (large.getDenominator().hash()));
//   }

  //Make sure we can properly handle:
  //http://www.ginac.de/CLN/cln_3.html#SEC15
  void testConstruction(){
    const int i_above2tothe29 = (1 << 29) + 1;
    const unsigned int u_above2tothe29 = (1 << 29) + 1;
    TS_ASSERT_EQUALS(Rational(i_above2tothe29), Rational((long)i_above2tothe29));
    TS_ASSERT_EQUALS(Rational(u_above2tothe29),
                     Rational((unsigned long)u_above2tothe29));

  }
};
