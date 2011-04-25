/*********************                                                        */
/*! \file cardinality_public.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-box testing of CVC4::Cardinality
 **
 ** Public-box testing of CVC4::Cardinality.
 **/

#include "util/cardinality.h"
#include "util/integer.h"

#include <string>
#include <sstream>

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
    TS_ASSERT_THROWS( invalid = Cardinality(-1), IllegalArgumentException);
    TS_ASSERT_THROWS( invalid = Cardinality(-2), IllegalArgumentException);
    TS_ASSERT_THROWS( invalid = Cardinality(Integer("-3983982192391747295721957")), IllegalArgumentException);
    invalid = one; // test assignment
    invalid = Cardinality(5); // test assignment to temporary

    Cardinality copy(one); // test copy
    Cardinality big(Integer("3983982192391747295721957"));
    Cardinality r(Cardinality::REALS);
    Cardinality i(Cardinality::INTEGERS);

    TS_ASSERT( zero < one );
    TS_ASSERT( one < two );
    TS_ASSERT( two < invalid );
    TS_ASSERT( invalid < big );
    TS_ASSERT( big < i );
    TS_ASSERT( i < r );

    TS_ASSERT( zero <= one );
    TS_ASSERT( zero <= zero );
    TS_ASSERT( one <= two );
    TS_ASSERT( one <= one );
    TS_ASSERT( two <= invalid );
    TS_ASSERT( two <= two );
    TS_ASSERT( invalid <= big );
    TS_ASSERT( invalid <= invalid );
    TS_ASSERT( big <= i );
    TS_ASSERT( big <= big );
    TS_ASSERT( i <= r );
    TS_ASSERT( i <= i );
    TS_ASSERT( r <= r );

    TS_ASSERT( zero == zero );
    TS_ASSERT( one == one );
    TS_ASSERT( two == two );
    TS_ASSERT( invalid == invalid );
    TS_ASSERT( copy == copy );
    TS_ASSERT( copy == one );
    TS_ASSERT( one == copy );
    TS_ASSERT( big == big );
    TS_ASSERT( i == i );
    TS_ASSERT( r == r );

    TS_ASSERT( zero != one );
    TS_ASSERT( one != two );
    TS_ASSERT( two != invalid );
    TS_ASSERT( copy != r );
    TS_ASSERT( copy != i );
    TS_ASSERT( big != i );
    TS_ASSERT( i != big );
    TS_ASSERT( big != zero );
    TS_ASSERT( r != i );
    TS_ASSERT( i != r );

    TS_ASSERT( r > zero );
    TS_ASSERT( r > one );
    TS_ASSERT( r > two );
    TS_ASSERT( r > copy );
    TS_ASSERT( r > invalid );
    TS_ASSERT( r > big );
    TS_ASSERT( r > i );
    TS_ASSERT( !( r > r ) );
    TS_ASSERT( r >= r );

    TS_ASSERT( zero.isFinite() );
    TS_ASSERT( one.isFinite() );
    TS_ASSERT( two.isFinite() );
    TS_ASSERT( copy.isFinite() );
    TS_ASSERT( invalid.isFinite() );
    TS_ASSERT( big.isFinite() );
    TS_ASSERT( !i.isFinite() );
    TS_ASSERT( !r.isFinite() );

    TS_ASSERT( zero.getFiniteCardinality() == 0 );
    TS_ASSERT( one.getFiniteCardinality() == 1 );
    TS_ASSERT( two.getFiniteCardinality() == 2 );
    TS_ASSERT( copy.getFiniteCardinality() == 1 );
    TS_ASSERT( invalid.getFiniteCardinality() == 5 );
    TS_ASSERT( big.getFiniteCardinality() == Integer("3983982192391747295721957") );
    TS_ASSERT_THROWS( i.getFiniteCardinality(), IllegalArgumentException );
    TS_ASSERT_THROWS( r.getFiniteCardinality(), IllegalArgumentException );

    TS_ASSERT_THROWS( zero.getBethNumber(), IllegalArgumentException );
    TS_ASSERT_THROWS( one.getBethNumber(), IllegalArgumentException );
    TS_ASSERT_THROWS( two.getBethNumber(), IllegalArgumentException );
    TS_ASSERT_THROWS( copy.getBethNumber(), IllegalArgumentException );
    TS_ASSERT_THROWS( invalid.getBethNumber(), IllegalArgumentException );
    TS_ASSERT_THROWS( big.getBethNumber(), IllegalArgumentException );
    TS_ASSERT( i.getBethNumber() == 0 );
    TS_ASSERT( r.getBethNumber() == 1 );

    TS_ASSERT( zero != Cardinality::INTEGERS );
    TS_ASSERT( one != Cardinality::INTEGERS );
    TS_ASSERT( two != Cardinality::INTEGERS );
    TS_ASSERT( copy != Cardinality::INTEGERS );
    TS_ASSERT( invalid != Cardinality::INTEGERS );
    TS_ASSERT( big != Cardinality::INTEGERS );
    TS_ASSERT( r != Cardinality::INTEGERS );
    TS_ASSERT( i == Cardinality::INTEGERS );

    TS_ASSERT( zero != Cardinality::REALS );
    TS_ASSERT( one != Cardinality::REALS );
    TS_ASSERT( two != Cardinality::REALS );
    TS_ASSERT( copy != Cardinality::REALS );
    TS_ASSERT( invalid != Cardinality::REALS );
    TS_ASSERT( big != Cardinality::REALS );
    TS_ASSERT( i != Cardinality::REALS );
    TS_ASSERT( r == Cardinality::REALS );

    // should work the other way too

    TS_ASSERT( Cardinality::INTEGERS != zero );
    TS_ASSERT( Cardinality::INTEGERS != one );
    TS_ASSERT( Cardinality::INTEGERS != two );
    TS_ASSERT( Cardinality::INTEGERS != copy );
    TS_ASSERT( Cardinality::INTEGERS != invalid );
    TS_ASSERT( Cardinality::INTEGERS != big );
    TS_ASSERT( Cardinality::INTEGERS != r );
    TS_ASSERT( Cardinality::INTEGERS == i );

    TS_ASSERT( Cardinality::REALS != zero );
    TS_ASSERT( Cardinality::REALS != one );
    TS_ASSERT( Cardinality::REALS != two );
    TS_ASSERT( Cardinality::REALS != copy );
    TS_ASSERT( Cardinality::REALS != invalid );
    TS_ASSERT( Cardinality::REALS != big );
    TS_ASSERT( Cardinality::REALS != i );
    TS_ASSERT( Cardinality::REALS == r );

    // finite cardinal arithmetic

    TS_ASSERT( zero + zero == zero );
    TS_ASSERT( zero * zero == zero );
    TS_ASSERT( (zero ^ zero) == one );
    TS_ASSERT( zero + one == one );
    TS_ASSERT( zero * one == zero );
    TS_ASSERT( (zero ^ one) == zero );
    TS_ASSERT( one + zero == one );
    TS_ASSERT( one * zero == zero );
    TS_ASSERT( (one ^ zero) == one );
    TS_ASSERT( two + two == 4 );
    TS_ASSERT( (two ^ two) == 4 );
    TS_ASSERT( two * two == 4 );
    TS_ASSERT( (two += two) == 4 );
    TS_ASSERT( two == 4 );
    TS_ASSERT( (two = 2) == 2 );
    TS_ASSERT( two == 2 );
    TS_ASSERT( (two *= 2) == 4 );
    TS_ASSERT( two == 4 );
    TS_ASSERT( ((two = 2) ^= 2) == 4 );
    TS_ASSERT( two == 4 );
    TS_ASSERT( (two = 2) == 2 );

    // infinite cardinal arithmetic

    Cardinality x = i, y = Cardinality(2)^x, z = Cardinality(2)^y;

    TS_ASSERT( x == i && y == r );
    TS_ASSERT( x != r && y != i );
    TS_ASSERT( x != z && y != z );
    TS_ASSERT( x.isCountable() && !x.isFinite() );
    TS_ASSERT( !y.isCountable() && !y.isFinite() );
    TS_ASSERT( !z.isCountable() && !z.isFinite() );

    TS_ASSERT( big < x );
    TS_ASSERT( x < y );
    TS_ASSERT( y < z );

    TS_ASSERT_THROWS( big.getBethNumber(), IllegalArgumentException );
    TS_ASSERT( x.getBethNumber() == 0 );
    TS_ASSERT( y.getBethNumber() == 1 );
    TS_ASSERT( z.getBethNumber() == 2 );

    TS_ASSERT( (zero ^ x) == zero );
    TS_ASSERT( (one ^ x) == one );
    TS_ASSERT( (two ^ x) == y && (two ^ x) != x );
    TS_ASSERT( (big ^ x) == y && (big ^ x) != x );
    TS_ASSERT( (two ^ x) == (big ^ x) );

    TS_ASSERT( (x ^ zero) == one );
    TS_ASSERT( (x ^ one) == x );
    TS_ASSERT( (x ^ two) == x );
    TS_ASSERT( (x ^ big) == x );
    TS_ASSERT( (x ^ big) == (x ^ two) );

    TS_ASSERT( (zero ^ y) == zero );
    TS_ASSERT( (one ^ y) == one );
    TS_ASSERT( (two ^ y) != x && (two ^ y) != y );
    TS_ASSERT( (big ^ y) != y && (big ^ y) != y );
    TS_ASSERT( (big ^ y).getBethNumber() == 2 );
    TS_ASSERT( (two ^ y) == (big ^ y) );

    TS_ASSERT( (y ^ zero) == one );
    TS_ASSERT( (y ^ one) == y );
    TS_ASSERT( (y ^ two) == y );
    TS_ASSERT( (y ^ big) == y );
    TS_ASSERT( (y ^ big) == (y ^ two) );

    TS_ASSERT( (x ^ x) == y );
    TS_ASSERT( (y ^ x) == y );
    TS_ASSERT( (x ^ y) == z );
    TS_ASSERT( (y ^ y) == z );
    TS_ASSERT( (z ^ x) == z );
    TS_ASSERT( (z ^ y) == z );
    TS_ASSERT( (zero ^ z) == 0 );
    TS_ASSERT( (z ^ zero) == 1 );
    TS_ASSERT( (z ^ 0) == 1 );
    TS_ASSERT( (two ^ z) > z );
    TS_ASSERT( (big ^ z) == (two ^ z) );
    TS_ASSERT( (x ^ z) == (two ^ z) );
    TS_ASSERT( (y ^ z) == (x ^ z) );
    TS_ASSERT( (z ^ z) == (x ^ z) );
    TS_ASSERT( (z ^ z).getBethNumber() == 3 );

  }/* testCardinalities() */

};/* class CardinalityPublic */
