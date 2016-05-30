/*********************                                                        */
/*! \file bitvector_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

  void testStringConstructor() {
    BitVector b1("0101",2);
    TS_ASSERT_EQUALS( 4u, b1.getSize() );
    TS_ASSERT_EQUALS( "0101", b1.toString() );
    TS_ASSERT_EQUALS( "5", b1.toString(10) );
    TS_ASSERT_EQUALS( "5", b1.toString(16) );

    BitVector b2("000001", 2);
    TS_ASSERT_EQUALS( 6u, b2.getSize() );
    TS_ASSERT_EQUALS( "000001", b2.toString() );
    TS_ASSERT_EQUALS( "1", b2.toString(10) );
    TS_ASSERT_EQUALS( "1", b2.toString(16) );

    BitVector b3("7f", 16);
    TS_ASSERT_EQUALS( 8u, b3.getSize() );
    TS_ASSERT_EQUALS( "01111111", b3.toString() );
    TS_ASSERT_EQUALS( "127", b3.toString(10) );
    TS_ASSERT_EQUALS( "7f", b3.toString(16) );

    BitVector b4("01a", 16);
    TS_ASSERT_EQUALS( 12u, b4.getSize() );
    TS_ASSERT_EQUALS( "000000011010", b4.toString() );
    TS_ASSERT_EQUALS( "26", b4.toString(10) );
    TS_ASSERT_EQUALS( "1a", b4.toString(16) );
  }
};
