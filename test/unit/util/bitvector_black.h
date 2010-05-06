/*********************                                                        */
/** bitvector_black.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
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

  void testStringConstructor() {
    BitVector b1("0101",2);
    TS_ASSERT_EQUALS( 4, b1.getSize() );
    TS_ASSERT_EQUALS( "0101", b1.toString() );
    TS_ASSERT_EQUALS( "5", b1.toString(10) );
    TS_ASSERT_EQUALS( "5", b1.toString(16) );

    BitVector b2("000001", 2);
    TS_ASSERT_EQUALS( 6, b2.getSize() );
    TS_ASSERT_EQUALS( "000001", b2.toString() );
    TS_ASSERT_EQUALS( "1", b2.toString(10) );
    TS_ASSERT_EQUALS( "1", b2.toString(16) );

    BitVector b3("7f", 16);
    TS_ASSERT_EQUALS( 8, b3.getSize() );
    TS_ASSERT_EQUALS( "01111111", b3.toString() );
    TS_ASSERT_EQUALS( "127", b3.toString(10) );
    TS_ASSERT_EQUALS( "7f", b3.toString(16) );

    BitVector b4("01a", 16);
    TS_ASSERT_EQUALS( 12, b4.getSize() );
    TS_ASSERT_EQUALS( "000000011010", b4.toString() );
    TS_ASSERT_EQUALS( "26", b4.toString(10) );
    TS_ASSERT_EQUALS( "1a", b4.toString(16) );
  }
};
