/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Implementations of the utility functions for working with floating point theories. ]]
 **
 **/

#include "util/floatingpoint.h"

#include "base/cvc4_assert.h"

namespace CVC4 {

FloatingPointSize::FloatingPointSize (unsigned _e, unsigned _s) : e(_e), s(_s)
{
  PrettyCheckArgument(validExponentSize(_e),_e,"Invalid exponent size : %d",_e);
  PrettyCheckArgument(validSignificandSize(_s),_s,"Invalid significand size : %d",_s);
}

FloatingPointSize::FloatingPointSize (const FloatingPointSize &old) : e(old.e), s(old.s)
{
  PrettyCheckArgument(validExponentSize(e),e,"Invalid exponent size : %d",e);
  PrettyCheckArgument(validSignificandSize(s),s,"Invalid significand size : %d",s);
}

void FloatingPointLiteral::unfinished (void) const {
  Unimplemented("Floating-point literals not yet implemented.");
}

  FloatingPoint::FloatingPoint (unsigned e, unsigned s, const BitVector &bv) :
    fpl(e,s,0.0),
    t(e,s) {}


  static FloatingPointLiteral constructorHelperBitVector (const FloatingPointSize &ct, const RoundingMode &rm, const BitVector &bv, bool signedBV) {
    if (signedBV) {
      return FloatingPointLiteral(2,2,0.0);
    } else {
      return FloatingPointLiteral(2,2,0.0);
    }
    Unreachable("Constructor helper broken");
  }
  
  FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode &rm, const BitVector &bv, bool signedBV) :
    fpl(constructorHelperBitVector(ct, rm, bv, signedBV)),
    t(ct) {}

  
  static FloatingPointLiteral constructorHelperRational (const FloatingPointSize &ct, const RoundingMode &rm, const Rational &ri) {
    Rational r(ri);
    Rational two(2,1);
    
    if (r.isZero()) {
      return FloatingPointLiteral(2,2,0.0);
    } else {
      //int negative = (r.sgn() < 0) ? 1 : 0;
      r = r.abs();

      // Compute the exponent
      Integer exp(0U);
      Integer inc(1U);
      Rational working(1,1);

      if (r == working) {

      } else if ( r < working ) {
	while (r < working) {
	  exp -= inc;
	  working /= two;
	}
      } else {
	while (r >= working) {
	  exp += inc;
	  working *= two;
	}
	exp -= inc;
	working /= two;
      }

      Assert(working <= r);
      Assert(r < working * two);

      // Work out the number of bits required to represent the exponent for a normal number
      unsigned expBits = 2; // No point starting with an invalid amount

      Integer doubleInt(2);
      if (exp.strictlyPositive()) {
	Integer representable(4);     // 1 more than exactly representable with expBits
	while (representable <= exp) {// hence <=
	  representable *= doubleInt;
	  ++expBits;
	}
      } else if (exp.strictlyNegative()) {
	Integer representable(-4);    // Exactly representable with expBits + sign
	                              // but -2^n and -(2^n - 1) are both subnormal
	while ((representable + doubleInt) > exp) {
	  representable *= doubleInt;
	  ++expBits;
	}
      }
      ++expBits; // To allow for sign

      BitVector exactExp(expBits, exp);

      
      
      // Compute the significand.
      unsigned sigBits = ct.significand() + 2; // guard and sticky bits
      BitVector sig(sigBits, 0U);
      BitVector one(sigBits, 1U);
      Rational workingSig(0,1);
      for (unsigned i = 0; i < sigBits - 1; ++i) {
	Rational mid(workingSig + working);

	if (mid <= r) {
	  sig = sig | one;
	  workingSig = mid;
	}

	sig = sig.leftShift(one);
	working /= two;
      }

      // Compute the sticky bit
      Rational remainder(r - workingSig);
      Assert(Rational(0,1) <= remainder);

      if (!remainder.isZero()) {
	sig = sig | one;
      }

      // Build an exact float
      FloatingPointSize exactFormat(expBits, sigBits);

      // A small subtlety... if the format has expBits the unpacked format
      // may have more to allow subnormals to be normalised.
      // Thus...
      Unreachable("no concrete implementation of FloatingPointLiteral");
    }
    Unreachable("Constructor helper broken");
  }
  
  FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode &rm, const Rational &r) :
    fpl(constructorHelperRational(ct, rm, r)),
    t(ct) {}

  
  FloatingPoint FloatingPoint::makeNaN (const FloatingPointSize &t) {
    return FloatingPoint(2, 2, BitVector(4U,0U));
  }

  FloatingPoint FloatingPoint::makeInf (const FloatingPointSize &t, bool sign) {
    return FloatingPoint(2, 2, BitVector(4U,0U));
  }

  FloatingPoint FloatingPoint::makeZero (const FloatingPointSize &t, bool sign) {
    return FloatingPoint(2, 2, BitVector(4U,0U));
  }


  /* Operations implemented using symfpu */
  FloatingPoint FloatingPoint::absolute (void) const {
    return *this;
  }
  
  FloatingPoint FloatingPoint::negate (void) const {
    return *this;
  }
  
  FloatingPoint FloatingPoint::plus (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return *this;
  }

  FloatingPoint FloatingPoint::sub (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return *this;
  }

  FloatingPoint FloatingPoint::mult (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return *this;
  }

  FloatingPoint FloatingPoint::fma (const RoundingMode &rm, const FloatingPoint &arg1, const FloatingPoint &arg2) const {
    Assert(this->t == arg1.t);
    Assert(this->t == arg2.t);
    return *this;
  }

  FloatingPoint FloatingPoint::div (const RoundingMode &rm, const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return *this;
  }

  FloatingPoint FloatingPoint::sqrt (const RoundingMode &rm) const {
    return *this;
  }

  FloatingPoint FloatingPoint::rti (const RoundingMode &rm) const {
    return *this;
  }

  FloatingPoint FloatingPoint::rem (const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return *this;
  }

  FloatingPoint FloatingPoint::maxTotal (const FloatingPoint &arg, bool zeroCaseLeft) const {
    Assert(this->t == arg.t);
    return *this;
  }
  
  FloatingPoint FloatingPoint::minTotal (const FloatingPoint &arg, bool zeroCaseLeft) const {
    Assert(this->t == arg.t);
    return *this;
  }

  FloatingPoint::PartialFloatingPoint FloatingPoint::max (const FloatingPoint &arg) const {
    FloatingPoint tmp(maxTotal(arg, true));
    return PartialFloatingPoint(tmp, tmp == maxTotal(arg, false));
  }

  FloatingPoint::PartialFloatingPoint FloatingPoint::min (const FloatingPoint &arg) const {
    FloatingPoint tmp(minTotal(arg, true));
    return PartialFloatingPoint(tmp, tmp == minTotal(arg, false));
  }

  bool FloatingPoint::operator ==(const FloatingPoint& fp) const {
    return ( (t == fp.t) );
  }

  bool FloatingPoint::operator <= (const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return false;
  }

  bool FloatingPoint::operator < (const FloatingPoint &arg) const {
    Assert(this->t == arg.t);
    return false;
  }

  bool FloatingPoint::isNormal (void) const {
    return false;
  }

  bool FloatingPoint::isSubnormal (void) const {
    return false;
  }

  bool FloatingPoint::isZero (void) const {
    return false;
  }

  bool FloatingPoint::isInfinite (void) const {
    return false;
  }

  bool FloatingPoint::isNaN (void) const {
    return false;
  }

  bool FloatingPoint::isNegative (void) const {
    return false;
  }

  bool FloatingPoint::isPositive (void) const {
    return false;
  }

  FloatingPoint FloatingPoint::convert (const FloatingPointSize &target, const RoundingMode &rm) const {
    return *this;
  }
  
  BitVector FloatingPoint::convertToBVTotal (BitVectorSize width, const RoundingMode &rm, bool signedBV, BitVector undefinedCase) const {
    if (signedBV)
      return undefinedCase;
    else
      return undefinedCase;
  }

  Rational FloatingPoint::convertToRationalTotal (Rational undefinedCase) const {
    PartialRational p(convertToRational());

    return p.second ? p.first : undefinedCase;
  }

  FloatingPoint::PartialBitVector FloatingPoint::convertToBV (BitVectorSize width, const RoundingMode &rm, bool signedBV) const {
    BitVector tmp(convertToBVTotal (width, rm, signedBV, BitVector(width, 0U)));
    BitVector confirm(convertToBVTotal (width, rm, signedBV, BitVector(width, 1U)));

    return PartialBitVector(tmp, tmp == confirm);
  }

  FloatingPoint::PartialRational FloatingPoint::convertToRational (void) const {
    if (this->isNaN() || this->isInfinite()) {
      return PartialRational(Rational(0U, 1U), false);
    }
    if (this->isZero()) {
      return PartialRational(Rational(0U, 1U), true);
      
    } else {

      Integer sign(0);
      Integer exp(0);
      Integer significand(0);
      Integer signedSignificand(sign * significand);
      
      // Only have pow(uint32_t) so we should check this.
      Assert(this->t.significand() <= 32);
      
      if (!(exp.strictlyNegative())) {
	Integer r(signedSignificand.multiplyByPow2(exp.toUnsignedInt()));
	return PartialRational(Rational(r), true);
      } else {
	Integer one(1U);
	Integer q(one.multiplyByPow2((-exp).toUnsignedInt()));
	Rational r(signedSignificand, q);
	return PartialRational(r, true);
      }
    }

    Unreachable("Convert float literal to real broken.");
  }

  BitVector FloatingPoint::pack (void) const {
    BitVector bv(4u,0u);
    return bv;
  }



}/* CVC4 namespace */
