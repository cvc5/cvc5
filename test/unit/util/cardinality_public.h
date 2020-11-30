/*********************                                                        */
/*! \file cardinality_public.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public-box testing of CVC4::Cardinality
 **
 ** Public-box testing of CVC4::Cardinality.
 **/

#include <sstream>
#include <string>

#include "util/integer.h"
#include "util/cardinality.h"

using namespace CVC4;
using namespace std;

class CardinalityPublic : public CxxTest::TestSuite {
  stringstream ss;

public:

  void testCardinalities() {
    Cardinality zero(0);
    Cardinality one(1);
    Cardinality two(2);

    Cardinality invalid(0);
    TS_ASSERT_THROWS(invalid = Cardinality(-1), IllegalArgumentException&);
    TS_ASSERT_THROWS(invalid = Cardinality(-2), IllegalArgumentException&);
    TS_ASSERT_THROWS(
        invalid = Cardinality(Integer("-3983982192391747295721957")),
        IllegalArgumentException&);
    invalid = one; // test assignment
    invalid = Cardinality(5); // test assignment to temporary

    Cardinality copy(one); // test copy
    Cardinality big(Integer("3983982192391747295721957"));
    Cardinality r(Cardinality::REALS);
    Cardinality i(Cardinality::INTEGERS);

    TS_ASSERT( zero.compare(one) == Cardinality::LESS );
    TS_ASSERT( one.compare(two) == Cardinality::LESS );
    TS_ASSERT( two.compare(invalid) == Cardinality::LESS );
    TS_ASSERT( invalid.compare(big) == Cardinality::LESS );
    TS_ASSERT( big.compare(i) == Cardinality::LESS );
    TS_ASSERT( i.compare(r) == Cardinality::LESS );

    TS_ASSERT( zero.compare(one) != Cardinality::GREATER );
    TS_ASSERT( zero.compare(zero) != Cardinality::GREATER );
    TS_ASSERT( one.compare(two) != Cardinality::GREATER );
    TS_ASSERT( one.compare(one) != Cardinality::GREATER );
    TS_ASSERT( two.compare(invalid) != Cardinality::GREATER );
    TS_ASSERT( two.compare(two) != Cardinality::GREATER );
    TS_ASSERT( invalid.compare(big) != Cardinality::GREATER );
    TS_ASSERT( invalid.compare(invalid) != Cardinality::GREATER );
    TS_ASSERT( big.compare(i) != Cardinality::GREATER );
    TS_ASSERT( big.compare(big) != Cardinality::GREATER );
    TS_ASSERT( i.compare(r) != Cardinality::GREATER );
    TS_ASSERT( i.compare(i) != Cardinality::GREATER );
    TS_ASSERT( r.compare(r) != Cardinality::GREATER );

    TS_ASSERT( zero.compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( one.compare(one) == Cardinality::EQUAL );
    TS_ASSERT( two.compare(two) == Cardinality::EQUAL );
    TS_ASSERT( invalid.compare(invalid) == Cardinality::EQUAL );
    TS_ASSERT( copy.compare(copy) == Cardinality::EQUAL );
    TS_ASSERT( copy.compare(one) == Cardinality::EQUAL );
    TS_ASSERT( one.compare(copy) == Cardinality::EQUAL );
    TS_ASSERT( big.compare(big) == Cardinality::UNKNOWN );
    TS_ASSERT( i.compare(i) == Cardinality::EQUAL );
    TS_ASSERT( r.compare(r) == Cardinality::EQUAL );

    TS_ASSERT( zero.compare(one) != Cardinality::EQUAL );
    TS_ASSERT( one.compare(two) != Cardinality::EQUAL );
    TS_ASSERT( two.compare(invalid) != Cardinality::EQUAL );
    TS_ASSERT( copy.compare(r) != Cardinality::EQUAL );
    TS_ASSERT( copy.compare(i) != Cardinality::EQUAL );
    TS_ASSERT( big.compare(i) != Cardinality::EQUAL );
    TS_ASSERT( i.compare(big) != Cardinality::EQUAL );
    TS_ASSERT( big.compare(zero) != Cardinality::EQUAL );
    TS_ASSERT( r.compare(i) != Cardinality::EQUAL );
    TS_ASSERT( i.compare(r) != Cardinality::EQUAL );

    TS_ASSERT( r.compare(zero) == Cardinality::GREATER );
    TS_ASSERT( r.compare(one) == Cardinality::GREATER );
    TS_ASSERT( r.compare(two) == Cardinality::GREATER );
    TS_ASSERT( r.compare(copy) == Cardinality::GREATER );
    TS_ASSERT( r.compare(invalid) == Cardinality::GREATER );
    TS_ASSERT( r.compare(big) == Cardinality::GREATER );
    TS_ASSERT( r.compare(i) == Cardinality::GREATER );
    TS_ASSERT( r.compare(r) != Cardinality::GREATER );
    TS_ASSERT( r.compare(r) != Cardinality::LESS );

    TS_ASSERT( zero.isFinite() );
    TS_ASSERT( one.isFinite() );
    TS_ASSERT( two.isFinite() );
    TS_ASSERT( copy.isFinite() );
    TS_ASSERT( invalid.isFinite() );
    TS_ASSERT( big.isFinite() );
    TS_ASSERT( !i.isFinite() );
    TS_ASSERT( !r.isFinite() );

    TS_ASSERT( !zero.isLargeFinite() );
    TS_ASSERT( !one.isLargeFinite() );
    TS_ASSERT( !two.isLargeFinite() );
    TS_ASSERT( !copy.isLargeFinite() );
    TS_ASSERT( !invalid.isLargeFinite() );
    TS_ASSERT( big.isLargeFinite() );
    TS_ASSERT( !i.isLargeFinite() );
    TS_ASSERT( !r.isLargeFinite() );

    TS_ASSERT( zero.getFiniteCardinality() == 0 );
    TS_ASSERT( one.getFiniteCardinality() == 1 );
    TS_ASSERT( two.getFiniteCardinality() == 2 );
    TS_ASSERT( copy.getFiniteCardinality() == 1 );
    TS_ASSERT( invalid.getFiniteCardinality() == 5 );
    TS_ASSERT_THROWS(big.getFiniteCardinality(), IllegalArgumentException&);
    TS_ASSERT_THROWS(i.getFiniteCardinality(), IllegalArgumentException&);
    TS_ASSERT_THROWS(r.getFiniteCardinality(), IllegalArgumentException&);

    TS_ASSERT_THROWS(zero.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT_THROWS(one.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT_THROWS(two.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT_THROWS(copy.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT_THROWS(invalid.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT_THROWS(big.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT( i.getBethNumber() == 0 );
    TS_ASSERT( r.getBethNumber() == 1 );

    TS_ASSERT( zero.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( one.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( two.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( copy.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( invalid.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( big.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( r.compare(Cardinality::INTEGERS) != Cardinality::EQUAL );
    TS_ASSERT( i.compare(Cardinality::INTEGERS) == Cardinality::EQUAL );

    TS_ASSERT( zero.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( one.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( two.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( copy.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( invalid.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( big.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( i.compare(Cardinality::REALS) != Cardinality::EQUAL );
    TS_ASSERT( r.compare(Cardinality::REALS) == Cardinality::EQUAL );

    // should work the other way too

    TS_ASSERT( Cardinality::INTEGERS.compare(zero) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(one) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(two) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(copy) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(invalid) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(big) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(r) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::INTEGERS.compare(i) == Cardinality::EQUAL );

    TS_ASSERT( Cardinality::REALS.compare(zero) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(one) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(two) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(copy) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(invalid) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(big) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(i) != Cardinality::EQUAL );
    TS_ASSERT( Cardinality::REALS.compare(r) == Cardinality::EQUAL );

    // finite cardinal arithmetic

    TS_ASSERT( (zero + zero).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (zero * zero).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (zero ^ zero).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (zero + one).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (zero * one).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (zero ^ one).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (one + zero).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (one * zero).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (one ^ zero).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (two + two).compare(4) == Cardinality::EQUAL );
    TS_ASSERT( (two ^ two).compare(4) == Cardinality::EQUAL );
    TS_ASSERT( (two * two).compare(4) == Cardinality::EQUAL );
    TS_ASSERT( (two += two).compare(4) == Cardinality::EQUAL );
    TS_ASSERT( two.compare(4) == Cardinality::EQUAL );
    TS_ASSERT( (two = 2).compare(2) == Cardinality::EQUAL );
    TS_ASSERT( two.compare(2) == Cardinality::EQUAL );
    TS_ASSERT( (two *= 2).compare(4) == Cardinality::EQUAL );
    TS_ASSERT( two.compare(4) == Cardinality::EQUAL );
    TS_ASSERT( ((two = 2) ^= 2).compare(4) == Cardinality::EQUAL );
    TS_ASSERT( two.compare(4) == Cardinality::EQUAL );
    TS_ASSERT( (two = 2).compare(2) == Cardinality::EQUAL );

    // infinite cardinal arithmetic

    Cardinality x = i, y = Cardinality(2)^x, z = Cardinality(2)^y;

    TS_ASSERT( x.compare(i) == Cardinality::EQUAL && y.compare(r) == Cardinality::EQUAL );
    TS_ASSERT( x.compare(r) != Cardinality::EQUAL && y.compare(i) != Cardinality::EQUAL );
    TS_ASSERT( x.compare(z) != Cardinality::EQUAL && y.compare(z) != Cardinality::EQUAL );
    TS_ASSERT( x.isCountable() && !x.isFinite() );
    TS_ASSERT( !y.isCountable() && !y.isFinite() );
    TS_ASSERT( !z.isCountable() && !z.isFinite() );

    TS_ASSERT( big.compare(x) == Cardinality::LESS );
    TS_ASSERT( x.compare(y) == Cardinality::LESS );
    TS_ASSERT( y.compare(z) == Cardinality::LESS );

    TS_ASSERT_THROWS(big.getBethNumber(), IllegalArgumentException&);
    TS_ASSERT( x.getBethNumber() == 0 );
    TS_ASSERT( y.getBethNumber() == 1 );
    TS_ASSERT( z.getBethNumber() == 2 );

    TS_ASSERT( (zero ^ x).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (one ^ x).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (two ^ x).compare(y) == Cardinality::EQUAL && (two ^ x).compare(x) != Cardinality::EQUAL );
    TS_ASSERT( (big ^ x).compare(y) == Cardinality::EQUAL && (big ^ x).compare(x) != Cardinality::EQUAL );
    TS_ASSERT( (two ^ x).compare(big ^ x) == Cardinality::EQUAL );

    TS_ASSERT( (x ^ zero).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (x ^ one).compare(x) == Cardinality::EQUAL );
    TS_ASSERT( (x ^ two).compare(x) == Cardinality::EQUAL );
    TS_ASSERT( (x ^ big).compare(x) == Cardinality::EQUAL );
    TS_ASSERT( (x ^ big).compare(x ^ two) == Cardinality::EQUAL );

    TS_ASSERT( (zero ^ y).compare(zero) == Cardinality::EQUAL );
    TS_ASSERT( (one ^ y).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (two ^ y).compare(x) != Cardinality::EQUAL && (two ^ y).compare(y) != Cardinality::EQUAL );
    TS_ASSERT( (big ^ y).compare(y) != Cardinality::EQUAL && (big ^ y).compare(y) != Cardinality::EQUAL );
    TS_ASSERT( (big ^ y).getBethNumber() == 2 );
    TS_ASSERT( (two ^ y).compare(big ^ y) == Cardinality::EQUAL );

    TS_ASSERT( (y ^ zero).compare(one) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ one).compare(y) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ two).compare(y) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ big).compare(y) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ big).compare(y ^ two) == Cardinality::EQUAL );

    TS_ASSERT( (x ^ x).compare(y) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ x).compare(y) == Cardinality::EQUAL );
    TS_ASSERT( (x ^ y).compare(z) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ y).compare(z) == Cardinality::EQUAL );
    TS_ASSERT( (z ^ x).compare(z) == Cardinality::EQUAL );
    TS_ASSERT( (z ^ y).compare(z) == Cardinality::EQUAL );
    TS_ASSERT( (zero ^ z).compare(0) == Cardinality::EQUAL );
    TS_ASSERT( (z ^ zero).compare(1) == Cardinality::EQUAL );
    TS_ASSERT( (z ^ 0).compare(1) == Cardinality::EQUAL );
    TS_ASSERT( (two ^ z).compare(z) == Cardinality::GREATER );
    TS_ASSERT( (big ^ z).compare(two ^ z) == Cardinality::EQUAL );
    TS_ASSERT( (x ^ z).compare(two ^ z) == Cardinality::EQUAL );
    TS_ASSERT( (y ^ z).compare(x ^ z) == Cardinality::EQUAL );
    TS_ASSERT( (z ^ z).compare(x ^ z) == Cardinality::EQUAL );
    TS_ASSERT( (z ^ z).getBethNumber() == 3 );

  }/* testCardinalities() */

};/* class CardinalityPublic */
