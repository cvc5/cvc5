/*********************                                                        */
/** rational_white.h
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


    Rational reduce3( 454789890342L, 273L);
    Integer num3(151596630114L);
    Integer den3(91);

    TS_ASSERT_EQUALS(reduce2.getNumerator(), num2);
    TS_ASSERT_EQUALS(reduce2.getDenominator(), den2);

    Rational reduce4( 454789890342L,-273L);
    Integer num4(-151596630114L);
    Integer den4(91);


    TS_ASSERT_EQUALS(reduce4.getNumerator(), num4);
    TS_ASSERT_EQUALS(reduce4.getDenominator(), den4);

    Rational reduce5(-454789890342L, 273L);
    Integer num5(-151596630114L);
    Integer den5(91);


    TS_ASSERT_EQUALS(reduce5.getNumerator(), num5);
    TS_ASSERT_EQUALS(reduce5.getDenominator(), den5);

    Rational reduce6(-454789890342L,-273L);
    Integer num6(151596630114L);
    Integer den6(91);


    TS_ASSERT_EQUALS(reduce6.getNumerator(), num6);
    TS_ASSERT_EQUALS(reduce6.getDenominator(), den6);

  }

  void testHash(){
    Rational large (canReduce);
    Rational zero;
    Rational one_word(75890L,590L);
    Rational two_words("7890D789D33234027890D789D3323402", 16);

    TS_ASSERT_EQUALS(zero.hash(), 1);
    TS_ASSERT_EQUALS(one_word.hash(), 7589 xor 59);
    TS_ASSERT_EQUALS(two_words.hash(), 9921844058862803974UL ^ 1);
    TS_ASSERT_EQUALS(large.hash(),
                     (large.getNumerator().hash())^(large.getDenominator().hash()));
  }
};
