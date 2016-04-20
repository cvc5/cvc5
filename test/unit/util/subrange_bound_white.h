/*********************                                                        */
/*! \file subrange_bound_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White-box testing of CVC4::SubrangeBound
 **
 ** White-box testing of CVC4::SubrangeBound.
 **/

#include <sstream>
#include <string>

#include "util/integer.h"
#include "util/subrange_bound.h"

using namespace CVC4;
using namespace std;

class SubrangeBoundWhite : public CxxTest::TestSuite {
  stringstream ss;

public:

  void testInfinite() {
    SubrangeBound b;
    TS_ASSERT( ! b.hasBound() );
    TS_ASSERT_THROWS( b.getBound(), IllegalArgumentException );
    ss.str(""); ss << b;
    TS_ASSERT_EQUALS( ss.str(), "_" );
  }

  void testZero() {
    SubrangeBound b1(0), b2(Integer("0")), b3(Integer("1"));
    TS_ASSERT( b1.hasBound() && b2.hasBound() && b3.hasBound() );
    TS_ASSERT( b1.getBound() == 0 && b2.getBound() == 0 && b3.getBound() == 1 );
    TS_ASSERT( b1 == b2 ); TS_ASSERT( b2 == b1 );
    TS_ASSERT( !(b1 == b3) ); TS_ASSERT( !(b3 == b1) );
    TS_ASSERT( !(b2 == b3) ); TS_ASSERT( !(b3 == b2) );
    TS_ASSERT( !(b1 != b2) ); TS_ASSERT( !(b2 != b1) );
    TS_ASSERT( b1 != b3 ); TS_ASSERT( b3 != b1 );
    TS_ASSERT( b2 != b3 ); TS_ASSERT( b3 != b2 );
    ss.str(""); ss << b1;
    TS_ASSERT( ss.str() == "0" );
    ss.str(""); ss << b2;
    TS_ASSERT( ss.str() == "0" );
    ss.str(""); ss << b3;
    TS_ASSERT( ss.str() == "1" );
  }

  void testOne() {
    SubrangeBound b(Integer("1"));
    TS_ASSERT( b.hasBound() );
    TS_ASSERT( b.getBound() == 1 );
    ss.str(""); ss << b;
    TS_ASSERT( ss.str() == "1" );
  }

  void testMinusOne() {
  }

  void testLarge() {
  }

  void testSmall() {
  }

};/* class SubrangeBoundWhite */
