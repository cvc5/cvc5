#include <cxxtest/TestSuite.h>

#include "util/real_algebraic_number.h"

using namespace CVC4;
using namespace std;

#ifndef CVC4_POLY_IMP
#error "This unit test should only be enabled for CVC4_POLY_IMP"
#endif

class RealAlgebraicNumberBlack : public CxxTest::TestSuite {
public:

  void test_creation() {
    TS_ASSERT(is_zero(RealAlgebraicNumber()));
    TS_ASSERT(is_one(RealAlgebraicNumber(Integer(1))));
    TS_ASSERT(!is_one(RealAlgebraicNumber(Rational(2))));
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);
    TS_ASSERT(RealAlgebraicNumber(Integer(1)) < sqrt2);
    TS_ASSERT(sqrt2 < RealAlgebraicNumber(Integer(2)));
  }

  void test_comparison() {
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

  void test_sgn() {
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber zero;
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);

    TS_ASSERT(sgn(msqrt2) == -1);
    TS_ASSERT(sgn(zero) == 0);
    TS_ASSERT(sgn(sqrt2) == 1);
  }

  void test_arithmetic() {
    RealAlgebraicNumber msqrt2({-2, 0, 1}, -2, -1);
    RealAlgebraicNumber zero;
    RealAlgebraicNumber sqrt2({-2, 0, 1}, 1, 2);

    TS_ASSERT(msqrt2 + sqrt2 == zero);
    TS_ASSERT(-msqrt2 == sqrt2);
    TS_ASSERT(-msqrt2 + sqrt2 == sqrt2 + sqrt2);
    //TS_ASSERT(-msqrt2 + sqrt2 == RealAlgebraicNumber(Integer(2)) * sqrt2);
    TS_ASSERT(msqrt2 * sqrt2 == RealAlgebraicNumber(Integer(-2)));
  }
};
