/*********************                                                        */
/*! \file integer_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Aina Niemetz, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Integer.
 **
 ** Black box testing of CVC4::Integer.
 **/

#include <cxxtest/TestSuite.h>

#include <limits>
#include <sstream>

#include "util/integer.h"

using namespace CVC4;
using namespace std;

const char* largeVal = "4547897890548754897897897897890789078907890";
const char* lotsOfLeadingZeroes = "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001";

class IntegerBlack : public CxxTest::TestSuite {


public:

  void testConstructors() {
    Integer z0(1);
    TS_ASSERT_EQUALS(z0.getLong(), 1);

    Integer z1(0);
    TS_ASSERT_EQUALS(z1.getLong(), 0);

    Integer z2(-1);
    TS_ASSERT_EQUALS(z2.getLong(), -1);

    Integer z3(0x890UL);
    TS_ASSERT_EQUALS(z3.getUnsignedLong(), 0x890UL);

    Integer z4;
    TS_ASSERT_EQUALS(z4.getLong(), 0);

    Integer z5("7896890");
    TS_ASSERT_EQUALS(z5.getUnsignedLong(), 7896890ul);

    Integer z6(z5);
    TS_ASSERT_EQUALS(z5.getUnsignedLong(), 7896890ul);
    TS_ASSERT_EQUALS(z6.getUnsignedLong(), 7896890ul);


    string bigValue("1536729");
    Integer z7(bigValue);
    TS_ASSERT_EQUALS(z7.getUnsignedLong(), 1536729ul);
  }

  void testCompareAgainstZero(){
    Integer z(0);
    TS_ASSERT_THROWS_NOTHING(z == 0;);
    TS_ASSERT_EQUALS(z,0);
  }

  void testOperatorAssign(){
    Integer x(0);
    Integer y(79);
    Integer z(45789);

    TS_ASSERT_EQUALS(x.getUnsignedLong(), 0ul);
    TS_ASSERT_EQUALS(y.getUnsignedLong(), 79ul);
    TS_ASSERT_EQUALS(z.getUnsignedLong(), 45789ul);

    x = y = z;

    TS_ASSERT_EQUALS(x.getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(y.getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(z.getUnsignedLong(), 45789ul);

    Integer a(2);

    y = a;

    TS_ASSERT_EQUALS(a.getUnsignedLong(), 2ul);
    TS_ASSERT_EQUALS(y.getUnsignedLong(), 2ul);
    TS_ASSERT_EQUALS(x.getUnsignedLong(), 45789ul);
    TS_ASSERT_EQUALS(z.getUnsignedLong(), 45789ul);
  }

  void testOperatorEquals(){
    Integer a(0);
    Integer b(79);
    Integer c("79");
    Integer d;

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
    Integer a(0);
    Integer b(79);
    Integer c("79");
    Integer d;

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


  void testToStringStuff(){
    stringstream ss;
    Integer large (largeVal);
    ss << large;
    string res = ss.str();

    TS_ASSERT_EQUALS(res, large.toString());
  }

  void testBaseInference() {
    TS_ASSERT_EQUALS(Integer("0xa", 0), 10);
    TS_ASSERT_EQUALS(Integer("0xff", 0), 255);
    TS_ASSERT_EQUALS(Integer("011", 0), 9);
    TS_ASSERT_EQUALS(Integer("0b1010", 0), 10);
    TS_ASSERT_EQUALS(Integer("-1", 0), -1);
    TS_ASSERT_EQUALS(Integer("42", 0), 42);
  }

  void testParseErrors() {
    TS_ASSERT_THROWS(Integer("abracadabra"), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("+-1"), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("-+1"), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("5i"), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("10xyz"), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("0xff", 10), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("#x5", 0), std::invalid_argument&);
    TS_ASSERT_THROWS(Integer("0b123", 0), std::invalid_argument&);
  }

  void testPow() {
    TS_ASSERT_EQUALS( Integer(1), Integer(1).pow(0) );
    TS_ASSERT_EQUALS( Integer(1), Integer(5).pow(0) );
    TS_ASSERT_EQUALS( Integer(1), Integer(-1).pow(0) );
    TS_ASSERT_EQUALS( Integer(0), Integer(0).pow(1) );
    TS_ASSERT_EQUALS( Integer(5), Integer(5).pow(1) );
    TS_ASSERT_EQUALS( Integer(-5), Integer(-5).pow(1) );
    TS_ASSERT_EQUALS( Integer(16), Integer(2).pow(4) );
    TS_ASSERT_EQUALS( Integer(16), Integer(-2).pow(4) );
    TS_ASSERT_EQUALS( Integer(1000), Integer(10).pow(3) );
    TS_ASSERT_EQUALS( Integer(-1000), Integer(-10).pow(3) );
  }

  void testOverlyLong() {
    unsigned long ul = numeric_limits<unsigned long>::max();
    Integer i(ul);
    TS_ASSERT(i.getUnsignedLong() == ul);
    TS_ASSERT_THROWS_ANYTHING(i.getLong());
    unsigned long ulplus1 = ul + 1;
    TS_ASSERT(ulplus1 == 0);
    i = i + 1;
    TS_ASSERT_THROWS_ANYTHING(i.getUnsignedLong());
  }

  void testTestBit() {
    TS_ASSERT( ! Integer(0).testBit(6) );
    TS_ASSERT( ! Integer(0).testBit(5) );
    TS_ASSERT( ! Integer(0).testBit(4) );
    TS_ASSERT( ! Integer(0).testBit(3) );
    TS_ASSERT( ! Integer(0).testBit(2) );
    TS_ASSERT( ! Integer(0).testBit(1) );
    TS_ASSERT( ! Integer(0).testBit(0) );

    TS_ASSERT( Integer(-1).testBit(6) );
    TS_ASSERT( Integer(-1).testBit(5) );
    TS_ASSERT( Integer(-1).testBit(4) );
    TS_ASSERT( Integer(-1).testBit(3) );
    TS_ASSERT( Integer(-1).testBit(2) );
    TS_ASSERT( Integer(-1).testBit(1) );
    TS_ASSERT( Integer(-1).testBit(0) );

    TS_ASSERT( ! Integer(10).testBit(6) );
    TS_ASSERT( ! Integer(10).testBit(5) );
    TS_ASSERT( ! Integer(10).testBit(4) );
    TS_ASSERT( Integer(10).testBit(3) );
    TS_ASSERT( ! Integer(10).testBit(2) );
    TS_ASSERT( Integer(10).testBit(1) );
    TS_ASSERT( ! Integer(10).testBit(0) );

    TS_ASSERT( ! Integer(14).testBit(6) );
    TS_ASSERT( ! Integer(14).testBit(5) );
    TS_ASSERT( ! Integer(14).testBit(4) );
    TS_ASSERT( Integer(14).testBit(3) );
    TS_ASSERT( Integer(14).testBit(2) );
    TS_ASSERT( Integer(14).testBit(1) );
    TS_ASSERT( ! Integer(14).testBit(0) );

    TS_ASSERT( Integer(64).testBit(6) );
    TS_ASSERT( ! Integer(64).testBit(5) );
    TS_ASSERT( ! Integer(64).testBit(4) );
    TS_ASSERT( ! Integer(64).testBit(3) );
    TS_ASSERT( ! Integer(64).testBit(2) );
    TS_ASSERT( ! Integer(64).testBit(1) );
    TS_ASSERT( ! Integer(64).testBit(0) );
  }

  unsigned int internalLength(int i){
    if ( i == 0){
      return 1;
    }else{
      int absi = i < 0 ? -i : i;
      unsigned int n = 0;
      int powN = 1;
      do {
        powN <<= 1;
        ++n;
      }while(absi >= powN);
      return n;
    }
  }

  void testTestLength() {
    for(int i = -17; i <= 17; ++i){
      TS_ASSERT_EQUALS(Integer(i).length(), internalLength(i));
    }
  }

  void testEuclideanDivision() {
    Integer q, r;

    Integer::euclidianQR(q, r, 1, 4);
    TS_ASSERT_EQUALS( q, Integer(0));
    TS_ASSERT_EQUALS( r, Integer(1));


    Integer::euclidianQR(q, r, 1, -4);
    TS_ASSERT_EQUALS( q, Integer(0));
    TS_ASSERT_EQUALS( r, Integer(1));

    Integer::euclidianQR(q, r, -1, 4);
    TS_ASSERT_EQUALS( q, Integer(-1));
    TS_ASSERT_EQUALS( r, Integer(3));

    Integer::euclidianQR(q,r, -1, -4);
    TS_ASSERT_EQUALS( q, Integer(1));
    TS_ASSERT_EQUALS( r, Integer(3));

    Integer::euclidianQR(q,r, 5, 4);
    TS_ASSERT_EQUALS( q, Integer(1));
    TS_ASSERT_EQUALS( r, Integer(1));

    Integer::euclidianQR(q,r, 5, -4);
    TS_ASSERT_EQUALS( q, Integer(-1));
    TS_ASSERT_EQUALS( r, Integer(1));

    Integer::euclidianQR(q,r, -5, 4);
    TS_ASSERT_EQUALS( q, Integer(-2));
    TS_ASSERT_EQUALS( r, Integer(3));

    Integer::euclidianQR(q,r, -5, -4);
    TS_ASSERT_EQUALS( q, Integer(2));
    TS_ASSERT_EQUALS( r, Integer(3));

  }
  void testFloorDivision() {
    Integer q, r;

    Integer::floorQR(q, r, 1, 4);
    TS_ASSERT_EQUALS( q, Integer(0));
    TS_ASSERT_EQUALS( r, Integer(1));


    Integer::floorQR(q, r, 1, -4);
    TS_ASSERT_EQUALS( q, Integer(-1));
    TS_ASSERT_EQUALS( r, Integer(-3));

    Integer::floorQR(q, r, -1, 4);
    TS_ASSERT_EQUALS( q, Integer(-1));
    TS_ASSERT_EQUALS( r, Integer(3));

    Integer::floorQR(q,r, -1, -4);
    TS_ASSERT_EQUALS( q, Integer(0));
    TS_ASSERT_EQUALS( r, Integer(-1));

    Integer::floorQR(q,r, 5, 4);
    TS_ASSERT_EQUALS( q, Integer(1));
    TS_ASSERT_EQUALS( r, Integer(1));

    Integer::floorQR(q,r, 5, -4);
    TS_ASSERT_EQUALS( q, Integer(-2));
    TS_ASSERT_EQUALS( r, Integer(-3));

    Integer::floorQR(q,r, -5, 4);
    TS_ASSERT_EQUALS( q, Integer(-2));
    TS_ASSERT_EQUALS( r, Integer(3));

    Integer::floorQR(q,r, -5, -4);
    TS_ASSERT_EQUALS( q, Integer(1));
    TS_ASSERT_EQUALS( r, Integer(-1));

  }

  void testLeadingZeroes() {
    string leadingZeroes(lotsOfLeadingZeroes);
    Integer one(1u);
    Integer one_from_string(leadingZeroes,2);
    TS_ASSERT_EQUALS(one, one_from_string);
  }

  void testModAdd()
  {
    for (unsigned i = 0; i <= 10; ++i)
    {
      for (unsigned j = 0; j <= 10; ++j)
      {
        Integer yy;
        Integer x(i);
        Integer y = x + j;
        Integer yp = x.modAdd(j, 3);
        for (yy = y; yy >= 3; yy -= 3)
          ;
        TS_ASSERT(yp == yy);
        yp = x.modAdd(j, 7);
        for (yy = y; yy >= 7; yy -= 7)
          ;
        TS_ASSERT(yp == yy);
        yp = x.modAdd(j, 11);
        for (yy = y; yy >= 11; yy -= 11)
          ;
        TS_ASSERT(yp == yy);
      }
    }
  }

  void testModMultiply()
  {
    for (unsigned i = 0; i <= 10; ++i)
    {
      for (unsigned j = 0; j <= 10; ++j)
      {
        Integer yy;
        Integer x(i);
        Integer y = x * j;
        Integer yp = x.modMultiply(j, 3);
        for (yy = y; yy >= 3; yy -= 3)
          ;
        TS_ASSERT(yp == yy);
        yp = x.modMultiply(j, 7);
        for (yy = y; yy >= 7; yy -= 7)
          ;
        TS_ASSERT(yp == yy);
        yp = x.modMultiply(j, 11);
        for (yy = y; yy >= 11; yy -= 11)
          ;
        TS_ASSERT(yp == yy);
      }
    }
  }

  void testModInverse()
  {
    for (unsigned i = 0; i <= 10; ++i)
    {
      Integer x(i);
      Integer inv = x.modInverse(3);
      if (i == 0 || i == 3 || i == 6 || i == 9)
      {
        TS_ASSERT(inv == -1); /* no inverse */
      }
      else
      {
        TS_ASSERT(x.modMultiply(inv, 3) == 1);
      }
      inv = x.modInverse(7);
      if (i == 0 || i == 7)
      {
        TS_ASSERT(inv == -1); /* no inverse */
      }
      else
      {
        TS_ASSERT(x.modMultiply(inv, 7) == 1);
      }
      inv = x.modInverse(11);
      if (i == 0)
      {
        TS_ASSERT(inv == -1); /* no inverse */
      }
      else
      {
        TS_ASSERT(x.modMultiply(inv, 11) == 1);
      }
    }
  }
};
