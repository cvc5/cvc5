/*********************                                                        */
/*! \file bitvector_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Christopher L. Conway, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::BitVector
 **
 ** Black box testing of CVC4::BitVector.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/bitvector.h"

using namespace CVC4;
using namespace std;

class BitVectorBlack : public CxxTest::TestSuite {


public:
 void setUp() override
 {
   zero = BitVector(4);
   one = zero.setBit(0);
   two = BitVector("0010", 2);
   negOne = BitVector(4, Integer(-1));
 }

 void testStringConstructor()
 {
   BitVector b1("0101", 2);
   TS_ASSERT_EQUALS(4u, b1.getSize());
   TS_ASSERT_EQUALS("0101", b1.toString());
   TS_ASSERT_EQUALS("5", b1.toString(10));
   TS_ASSERT_EQUALS("5", b1.toString(16));

   BitVector b2("000001", 2);
   TS_ASSERT_EQUALS(6u, b2.getSize());
   TS_ASSERT_EQUALS("000001", b2.toString());
   TS_ASSERT_EQUALS("1", b2.toString(10));
   TS_ASSERT_EQUALS("1", b2.toString(16));

   BitVector b3("7f", 16);
   TS_ASSERT_EQUALS(8u, b3.getSize());
   TS_ASSERT_EQUALS("01111111", b3.toString());
   TS_ASSERT_EQUALS("127", b3.toString(10));
   TS_ASSERT_EQUALS("7f", b3.toString(16));

   BitVector b4("01a", 16);
   TS_ASSERT_EQUALS(12u, b4.getSize());
   TS_ASSERT_EQUALS("000000011010", b4.toString());
   TS_ASSERT_EQUALS("26", b4.toString(10));
   TS_ASSERT_EQUALS("1a", b4.toString(16));
  }

  void testConversions()
  {
    TS_ASSERT_EQUALS(two.toSignedInteger(), Integer(2));
    TS_ASSERT_EQUALS(negOne.toString(), "1111");
    TS_ASSERT_EQUALS(negOne.getValue(), Integer(15));
    TS_ASSERT_EQUALS(negOne.getSize(), 4);
    TS_ASSERT_EQUALS(negOne.toInteger(), Integer(15));
    TS_ASSERT_EQUALS(negOne.toSignedInteger(), Integer(-1));

    TS_ASSERT_EQUALS(zero.hash(), (one - one).hash());
    TS_ASSERT_DIFFERS(negOne.hash(), zero.hash());
  }

  void testSetGetBit()
  {
    TS_ASSERT_EQUALS(one.setBit(1).setBit(2).setBit(3), negOne);

    TS_ASSERT(negOne.isBitSet(3));
    TS_ASSERT(!two.isBitSet(3));

    TS_ASSERT_EQUALS(one.getValue(), Integer(1));
    TS_ASSERT_EQUALS(zero.isPow2(), 0);
    TS_ASSERT_EQUALS(one.isPow2(), 1);
    TS_ASSERT_EQUALS(two.isPow2(), 2);
    TS_ASSERT_EQUALS(negOne.isPow2(), 0);
  }

  void testConcatExtract()
  {
    BitVector b = one.concat(zero);
    TS_ASSERT_EQUALS(b.toString(), "00010000");
    TS_ASSERT_EQUALS(b.extract(7, 4), one);
    TS_ASSERT_THROWS(b.extract(4, 7), IllegalArgumentException&);
    TS_ASSERT_THROWS(b.extract(8, 3), IllegalArgumentException&);
    TS_ASSERT_EQUALS(b.concat(BitVector()), b);
  }

  void testComparisons()
  {
    TS_ASSERT_DIFFERS(zero, one);
    TS_ASSERT(negOne > zero);
    TS_ASSERT(negOne >= zero);
    TS_ASSERT(negOne >= negOne);
    TS_ASSERT(negOne == negOne);
    TS_ASSERT(zero.unsignedLessThan(negOne));
    TS_ASSERT(zero.unsignedLessThanEq(negOne));
    TS_ASSERT(zero.unsignedLessThanEq(zero));
    TS_ASSERT(zero < negOne);
    TS_ASSERT(zero <= negOne);
    TS_ASSERT(zero <= zero);
    TS_ASSERT(negOne.signedLessThan(zero));
    TS_ASSERT(negOne.signedLessThanEq(zero));
    TS_ASSERT(negOne.signedLessThanEq(negOne));

    BitVector b = negOne.concat(negOne);
    TS_ASSERT_THROWS(b.unsignedLessThan(negOne), IllegalArgumentException&);
    TS_ASSERT_THROWS(negOne.unsignedLessThanEq(b), IllegalArgumentException&);
    TS_ASSERT_THROWS(b.signedLessThan(negOne), IllegalArgumentException&);
    TS_ASSERT_THROWS(negOne.signedLessThanEq(b), IllegalArgumentException&);
  }

  void testBitwiseOps()
  {
    TS_ASSERT_EQUALS((one ^ negOne).toString(), "1110");
    TS_ASSERT_EQUALS((two | one).toString(), "0011");
    TS_ASSERT_EQUALS((negOne & two).toString(), "0010");
    TS_ASSERT_EQUALS((~two).toString(), "1101");
  }

  void testArithmetic()
  {
    TS_ASSERT_EQUALS(negOne + one, zero);
    TS_ASSERT_EQUALS((negOne - one).getValue(), Integer(14));
    TS_ASSERT_EQUALS((-negOne).getValue(), Integer(1));

    TS_ASSERT_EQUALS((two * (two + one)).getValue(), Integer(6));

    TS_ASSERT_EQUALS(two.unsignedDivTotal(zero), negOne);
    TS_ASSERT_EQUALS(negOne.unsignedDivTotal(two).getValue(), Integer(7));

    TS_ASSERT_EQUALS(two.unsignedRemTotal(zero), two);
    TS_ASSERT_EQUALS(negOne.unsignedRemTotal(two), one);

    BitVector b = negOne.concat(negOne);
    TS_ASSERT_THROWS(b + negOne, IllegalArgumentException&);
    TS_ASSERT_THROWS(negOne * b, IllegalArgumentException&);
    TS_ASSERT_THROWS(b.unsignedDivTotal(negOne), IllegalArgumentException&);
    TS_ASSERT_THROWS(negOne.unsignedRemTotal(b), IllegalArgumentException&);
  }

  void testExtendOps()
  {
    TS_ASSERT_EQUALS(one.zeroExtend(4), zero.concat(one));
    TS_ASSERT_EQUALS(one.zeroExtend(0), one);
    TS_ASSERT_EQUALS(negOne.signExtend(4), negOne.concat(negOne));
    TS_ASSERT_EQUALS(one.signExtend(4), zero.concat(one));
    TS_ASSERT_EQUALS(one.signExtend(0), one);
  }

  void testShifts()
  {
    TS_ASSERT_EQUALS(one.leftShift(one), two);
    TS_ASSERT_EQUALS(one.leftShift(negOne), zero);
    TS_ASSERT_EQUALS(one.leftShift(zero), one);

    TS_ASSERT_EQUALS(two.logicalRightShift(one), one);
    TS_ASSERT_EQUALS(two.logicalRightShift(negOne), zero);

    TS_ASSERT_EQUALS(two.arithRightShift(one), one);
    TS_ASSERT_EQUALS(negOne.arithRightShift(one), negOne);
    TS_ASSERT_EQUALS(negOne.arithRightShift(negOne), negOne);
    TS_ASSERT_EQUALS(two.arithRightShift(negOne), zero);
  }

  void testStaticHelpers()
  {
    TS_ASSERT_EQUALS(BitVector::mkOnes(4), negOne);
    TS_ASSERT_EQUALS(BitVector::mkMinSigned(4).toSignedInteger(), Integer(-8));
    TS_ASSERT_EQUALS(BitVector::mkMaxSigned(4).toSignedInteger(), Integer(7));
  }

 private:
  BitVector zero;
  BitVector one;
  BitVector two;
  BitVector negOne;
};
