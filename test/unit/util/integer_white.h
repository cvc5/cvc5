/*********************                                                        */
/** integer_white.h
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
    Integer one_word(75890);
    Integer two_words("7890D789D33234027890D789D3323402", 16);

    TS_ASSERT_EQUALS(zero.hash(), 0);
    TS_ASSERT_EQUALS(one_word.hash(), 75890);
    TS_ASSERT_EQUALS(two_words.hash(), 9921844058862803974UL);
    TS_ASSERT_EQUALS(large.hash(), 772190219532412699UL);
  }
};
