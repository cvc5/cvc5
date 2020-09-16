/*********************                                                        */
/*! \file integer_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::Integer.
 **
 ** White box testing of CVC4::Integer.
 **/

#include <cxxtest/TestSuite.h>
#include <sstream>

#include "util/integer.h"

using namespace CVC4;
using namespace std;

const char* largeVal = "4547897890548754897897897897890789078907890";


class IntegerWhite : public CxxTest::TestSuite {
public:

  void testHash(){
    Integer large (largeVal);
    Integer zero;
    Integer fits_in_2_bytes(55890);
    Integer fits_in_16_bytes("7890D789D33234027890D789D3323402", 16);


    TS_ASSERT_THROWS_NOTHING(zero.hash());
    TS_ASSERT_THROWS_NOTHING(fits_in_2_bytes.hash());
    TS_ASSERT_THROWS_NOTHING(fits_in_16_bytes.hash());
    TS_ASSERT_THROWS_NOTHING(large.hash());
  }

  //Make sure we can properly handle:
  //http://www.ginac.de/CLN/cln_3.html#SEC15
  void testConstruction(){
    const int i_above2tothe29 = (1 << 29) + 1;
    const unsigned int u_above2tothe29 = (1 << 29) + 1;
    TS_ASSERT_EQUALS(Integer(i_above2tothe29), Integer((long)i_above2tothe29));
    TS_ASSERT_EQUALS(Integer(u_above2tothe29),
                     Integer((unsigned long)u_above2tothe29));

  }
};
