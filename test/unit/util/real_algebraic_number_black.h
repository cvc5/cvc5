/*********************                                                        */
/*! \file real_algebraic_number_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::RealAlgebraicNumber.
 **
 ** Black box testing of CVC4::RealAlgebraicNumber.
 **/

#include <cxxtest/TestSuite.h>

#include "util/real_algebraic_number.h"

using namespace CVC4;
using namespace std;

#ifndef CVC4_POLY_IMP
#error "This unit test should only be enabled for CVC4_POLY_IMP"
#endif

class RealAlgebraicNumberBlack : public CxxTest::TestSuite
{
 public:
  void testCreation()
  {
    TS_ASSERT(isZero(RealAlgebraicNumber()));
    TS_ASSERT(isOne(RealAlgebraicNumber(Integer(1))));
    TS_ASSERT(!isOne(RealAlgebraicNumber(Rational(2))));
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
    TS_ASSERT(RealAlgebraicNumber(Integer(1)) < sqrt2);
    TS_ASSERT(sqrt2 < RealAlgebraicNumber(Integer(2)));
  }

  void testComparison()
  {
    RealAlgebraicNumber msqrt3({-3, 0, 1}, -2, -1);
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber zero;
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
    RealAlgebraicNumber sqrt3({-3, 0, 1}, 1, 2);

    TS_ASSERT(msqrt3 < msqrt2);
    TS_ASSERT(msqrt3 < zero);
    TS_ASSERT(msqrt3 < sqrt2);
    TS_ASSERT(msqrt3 < sqrt3);
    TS_ASSERT(msqrt2 < zero);
    TS_ASSERT(msqrt2 < sqrt2);
    TS_ASSERT(msqrt2 < sqrt3);
    TS_ASSERT(zero < sqrt2);
    TS_ASSERT(zero < sqrt3);
    TS_ASSERT(sqrt2 < sqrt3);
  }

  void testSgn()
  {
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber zero;
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);

    TS_ASSERT_EQUALS(sgn(msqrt2), -1);
    TS_ASSERT_EQUALS(sgn(zero), 0);
    TS_ASSERT_EQUALS(sgn(sqrt2), 1);
  }

  void testArithmetic()
  {
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber zero;
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);

    TS_ASSERT_EQUALS(msqrt2 + sqrt2, zero);
    TS_ASSERT_EQUALS(-msqrt2, sqrt2);
    TS_ASSERT_EQUALS(-msqrt2 + sqrt2, sqrt2 + sqrt2);
    TS_ASSERT_EQUALS(msqrt2 * sqrt2, RealAlgebraicNumber(Integer(-2)));
  }
};
