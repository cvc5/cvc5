/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Haniel Barbosa, Mathias Preiner
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Implementations of the utility functions for working with floating point theories. ]]
 **
 **/

#include "util/floatingpoint.h"
#include "base/check.h"
#include "util/integer.h"

#include <math.h>
#include <limits>

#ifdef CVC4_USE_SYMFPU
#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/utils/numberOfRoundingModes.h"
#include "symfpu/utils/properties.h"
#endif

#ifdef CVC4_USE_SYMFPU
namespace symfpu {

#define CVC4_LIT_ITE_DFN(T)                                        \
  template <>                                                      \
  struct ite<::CVC4::symfpuLiteral::prop, T>                       \
  {                                                                \
    static const T &iteOp(const ::CVC4::symfpuLiteral::prop &cond, \
                          const T &l,                              \
                          const T &r)                              \
    {                                                              \
      return cond ? l : r;                                         \
    }                                                              \
  }

CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::rm);
CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::prop);
CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::sbv);
CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::ubv);

#undef CVC4_LIT_ITE_DFN
}
#endif

#ifndef CVC4_USE_SYMFPU
#define PRECONDITION(X) Assert((X))
#endif

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

namespace symfpuLiteral {

// To simplify the property macros
typedef traits t;

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::one(const bwt &w)
{
  return wrappedBitVector<isSigned>(w, 1);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::zero(const bwt &w)
{
  return wrappedBitVector<isSigned>(w, 0);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::allOnes(const bwt &w)
{
  return ~wrappedBitVector<isSigned>::zero(w);
}

template <bool isSigned>
prop wrappedBitVector<isSigned>::isAllOnes() const
{
  return (*this == wrappedBitVector<isSigned>::allOnes(this->getWidth()));
}
template <bool isSigned>
prop wrappedBitVector<isSigned>::isAllZeros() const
{
  return (*this == wrappedBitVector<isSigned>::zero(this->getWidth()));
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::maxValue(const bwt &w)
{
  if (isSigned)
  {
    BitVector base(w - 1, 0U);
    return wrappedBitVector<true>((~base).zeroExtend(1));
  }
  else
  {
    return wrappedBitVector<false>::allOnes(w);
  }
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::minValue(const bwt &w)
{
  if (isSigned)
  {
    BitVector base(w, 1U);
    BitVector shiftAmount(w, w - 1);
    BitVector result(base.leftShift(shiftAmount));
    return wrappedBitVector<true>(result);
  }
  else
  {
    return wrappedBitVector<false>::zero(w);
  }
}

/*** Operators ***/
template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator<<(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::leftShift(op);
}

template <>
wrappedBitVector<true> wrappedBitVector<true>::operator>>(
    const wrappedBitVector<true> &op) const
{
  return this->BitVector::arithRightShift(op);
}

template <>
wrappedBitVector<false> wrappedBitVector<false>::operator>>(
    const wrappedBitVector<false> &op) const
{
  return this->BitVector::logicalRightShift(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator|(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::operator|(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator&(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::operator&(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator+(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::operator+(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator-(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::operator-(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator*(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::operator*(op);
}

template <>
wrappedBitVector<false> wrappedBitVector<false>::operator/(
    const wrappedBitVector<false> &op) const
{
  return this->BitVector::unsignedDivTotal(op);
}

template <>
wrappedBitVector<false> wrappedBitVector<false>::operator%(
    const wrappedBitVector<false> &op) const
{
  return this->BitVector::unsignedRemTotal(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator-(void) const
{
  return this->BitVector::operator-();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator~(void)const
{
  return this->BitVector::operator~();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::increment() const
{
  return *this + wrappedBitVector<isSigned>::one(this->getWidth());
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::decrement() const
{
  return *this - wrappedBitVector<isSigned>::one(this->getWidth());
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::signExtendRightShift(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::arithRightShift(BitVector(this->getWidth(), op));
}

/*** Modular opertaions ***/
// No overflow checking so these are the same as other operations
template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularLeftShift(
    const wrappedBitVector<isSigned> &op) const
{
  return *this << op;
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularRightShift(
    const wrappedBitVector<isSigned> &op) const
{
  return *this >> op;
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularIncrement() const
{
  return this->increment();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularDecrement() const
{
  return this->decrement();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularAdd(
    const wrappedBitVector<isSigned> &op) const
{
  return *this + op;
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularNegate() const
{
  return -(*this);
}

/*** Comparisons ***/

template <bool isSigned>
prop wrappedBitVector<isSigned>::operator==(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::operator==(op);
}

template <>
prop wrappedBitVector<true>::operator<=(const wrappedBitVector<true> &op) const
{
  return this->signedLessThanEq(op);
}

template <>
prop wrappedBitVector<true>::operator>=(const wrappedBitVector<true> &op) const
{
  return !(this->signedLessThan(op));
}

template <>
prop wrappedBitVector<true>::operator<(const wrappedBitVector<true> &op) const
{
  return this->signedLessThan(op);
}

template <>
prop wrappedBitVector<true>::operator>(const wrappedBitVector<true> &op) const
{
  return !(this->signedLessThanEq(op));
}

template <>
prop wrappedBitVector<false>::operator<=(
    const wrappedBitVector<false> &op) const
{
  return this->unsignedLessThanEq(op);
}

template <>
prop wrappedBitVector<false>::operator>=(
    const wrappedBitVector<false> &op) const
{
  return !(this->unsignedLessThan(op));
}

template <>
prop wrappedBitVector<false>::operator<(const wrappedBitVector<false> &op) const
{
  return this->unsignedLessThan(op);
}

template <>
prop wrappedBitVector<false>::operator>(const wrappedBitVector<false> &op) const
{
  return !(this->unsignedLessThanEq(op));
}

/*** Type conversion ***/
// CVC4 nodes make no distinction between signed and unsigned, thus ...
template <bool isSigned>
wrappedBitVector<true> wrappedBitVector<isSigned>::toSigned(void) const
{
  return wrappedBitVector<true>(*this);
}

template <bool isSigned>
wrappedBitVector<false> wrappedBitVector<isSigned>::toUnsigned(void) const
{
  return wrappedBitVector<false>(*this);
}

/*** Bit hacks ***/

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::extend(
    bwt extension) const
{
  if (isSigned)
  {
    return this->BitVector::signExtend(extension);
  }
  else
  {
    return this->BitVector::zeroExtend(extension);
  }
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::contract(
    bwt reduction) const
{
  PRECONDITION(this->getWidth() > reduction);

  return this->extract((this->getWidth() - 1) - reduction, 0);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::resize(bwt newSize) const
{
  bwt width = this->getWidth();

  if (newSize > width)
  {
    return this->extend(newSize - width);
  }
  else if (newSize < width)
  {
    return this->contract(width - newSize);
  }
  else
  {
    return *this;
  }
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::matchWidth(
    const wrappedBitVector<isSigned> &op) const
{
  PRECONDITION(this->getWidth() <= op.getWidth());
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::append(
    const wrappedBitVector<isSigned> &op) const
{
  return this->BitVector::concat(op);
}

// Inclusive of end points, thus if the same, extracts just one bit
template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::extract(bwt upper,
                                                               bwt lower) const
{
  PRECONDITION(upper >= lower);
  return this->BitVector::extract(upper, lower);
}

// Explicit instantiation
template class wrappedBitVector<true>;
template class wrappedBitVector<false>;

rm traits::RNE(void) { return ::CVC4::roundNearestTiesToEven; };
rm traits::RNA(void) { return ::CVC4::roundNearestTiesToAway; };
rm traits::RTP(void) { return ::CVC4::roundTowardPositive; };
rm traits::RTN(void) { return ::CVC4::roundTowardNegative; };
rm traits::RTZ(void) { return ::CVC4::roundTowardZero; };
// This is a literal back-end so props are actually bools
// so these can be handled in the same way as the internal assertions above

void traits::precondition(const prop &p)
{
  Assert(p);
  return;
}
void traits::postcondition(const prop &p)
{
  Assert(p);
  return;
}
void traits::invariant(const prop &p)
{
  Assert(p);
  return;
}
}

#ifndef CVC4_USE_SYMFPU
void FloatingPointLiteral::unfinished(void) const
{
  Unimplemented() << "Floating-point literals not yet implemented.";
}
#endif

FloatingPoint::FloatingPoint(unsigned e, unsigned s, const BitVector &bv)
    :
#ifdef CVC4_USE_SYMFPU
      fpl(symfpu::unpack<symfpuLiteral::traits>(symfpuLiteral::fpt(e, s), bv)),
#else
      fpl(e, s, 0.0),
#endif
      t(e, s)
{
}

static FloatingPointLiteral constructorHelperBitVector(
    const FloatingPointSize &ct,
    const RoundingMode &rm,
    const BitVector &bv,
    bool signedBV)
{
#ifdef CVC4_USE_SYMFPU
  if (signedBV)
  {
    return FloatingPointLiteral(
        symfpu::convertSBVToFloat<symfpuLiteral::traits>(
            symfpuLiteral::fpt(ct),
            symfpuLiteral::rm(rm),
            symfpuLiteral::sbv(bv)));
  }
  else
  {
    return FloatingPointLiteral(
        symfpu::convertUBVToFloat<symfpuLiteral::traits>(
            symfpuLiteral::fpt(ct),
            symfpuLiteral::rm(rm),
            symfpuLiteral::ubv(bv)));
  }
#else
  return FloatingPointLiteral(2, 2, 0.0);
#endif
  Unreachable() << "Constructor helper broken";
  }
  
  FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode &rm, const BitVector &bv, bool signedBV) :
    fpl(constructorHelperBitVector(ct, rm, bv, signedBV)),
    t(ct) {}

  
  static FloatingPointLiteral constructorHelperRational (const FloatingPointSize &ct, const RoundingMode &rm, const Rational &ri) {
    Rational r(ri);
    Rational two(2,1);
    
    if (r.isZero()) {
#ifdef CVC4_USE_SYMFPU
      return FloatingPointLiteral::makeZero(
          ct, false);  // In keeping with the SMT-LIB standard
#else
      return FloatingPointLiteral(2,2,0.0);
#endif
    } else {
#ifdef CVC4_USE_SYMFPU
      int negative = (r.sgn() < 0) ? 1 : 0;
#endif
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
      unsigned sigBits = ct.significandWidth() + 2;  // guard and sticky bits
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
      Assert(Rational(0, 1) <= remainder);

      if (!remainder.isZero()) {
	sig = sig | one;
      }

      // Build an exact float
      FloatingPointSize exactFormat(expBits, sigBits);

      // A small subtlety... if the format has expBits the unpacked format
      // may have more to allow subnormals to be normalised.
      // Thus...
#ifdef CVC4_USE_SYMFPU
      unsigned extension =
          FloatingPointLiteral::exponentWidth(exactFormat) - expBits;

      FloatingPointLiteral exactFloat(
          negative, exactExp.signExtend(extension), sig);

      // Then cast...
      FloatingPointLiteral rounded(
          symfpu::convertFloatToFloat(exactFormat, ct, rm, exactFloat));
      return rounded;
#else
      Unreachable() << "no concrete implementation of FloatingPointLiteral";
#endif
    }
    Unreachable() << "Constructor helper broken";
  }
  
  FloatingPoint::FloatingPoint (const FloatingPointSize &ct, const RoundingMode &rm, const Rational &r) :
    fpl(constructorHelperRational(ct, rm, r)),
    t(ct) {}

  
  FloatingPoint FloatingPoint::makeNaN (const FloatingPointSize &t) {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(
        t, symfpu::unpackedFloat<symfpuLiteral::traits>::makeNaN(t));
#else
    return FloatingPoint(2, 2, BitVector(4U,0U));
#endif
  }

  FloatingPoint FloatingPoint::makeInf (const FloatingPointSize &t, bool sign) {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(
        t, symfpu::unpackedFloat<symfpuLiteral::traits>::makeInf(t, sign));
#else
    return FloatingPoint(2, 2, BitVector(4U,0U));
#endif
  }

  FloatingPoint FloatingPoint::makeZero (const FloatingPointSize &t, bool sign) {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(
        t, symfpu::unpackedFloat<symfpuLiteral::traits>::makeZero(t, sign));
#else
    return FloatingPoint(2, 2, BitVector(4U,0U));
#endif
  }


  /* Operations implemented using symfpu */
  FloatingPoint FloatingPoint::absolute (void) const {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(t, symfpu::absolute<symfpuLiteral::traits>(t, fpl));
#else
    return *this;
#endif
  }
  
  FloatingPoint FloatingPoint::negate (void) const {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(t, symfpu::negate<symfpuLiteral::traits>(t, fpl));
#else
    return *this;
#endif
  }
  
  FloatingPoint FloatingPoint::plus (const RoundingMode &rm, const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::add<symfpuLiteral::traits>(t, rm, fpl, arg.fpl, true));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::sub (const RoundingMode &rm, const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::add<symfpuLiteral::traits>(t, rm, fpl, arg.fpl, false));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::mult (const RoundingMode &rm, const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::multiply<symfpuLiteral::traits>(t, rm, fpl, arg.fpl));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::fma (const RoundingMode &rm, const FloatingPoint &arg1, const FloatingPoint &arg2) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg1.t);
    Assert(this->t == arg2.t);
    return FloatingPoint(
        t, symfpu::fma<symfpuLiteral::traits>(t, rm, fpl, arg1.fpl, arg2.fpl));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::div (const RoundingMode &rm, const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::divide<symfpuLiteral::traits>(t, rm, fpl, arg.fpl));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::sqrt (const RoundingMode &rm) const {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(t, symfpu::sqrt<symfpuLiteral::traits>(t, rm, fpl));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::rti (const RoundingMode &rm) const {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(
        t, symfpu::roundToIntegral<symfpuLiteral::traits>(t, rm, fpl));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::rem (const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::remainder<symfpuLiteral::traits>(t, fpl, arg.fpl));
#else
    return *this;
#endif
  }

  FloatingPoint FloatingPoint::maxTotal (const FloatingPoint &arg, bool zeroCaseLeft) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::max<symfpuLiteral::traits>(t, fpl, arg.fpl, zeroCaseLeft));
#else
    return *this;
#endif
  }
  
  FloatingPoint FloatingPoint::minTotal (const FloatingPoint &arg, bool zeroCaseLeft) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return FloatingPoint(
        t, symfpu::min<symfpuLiteral::traits>(t, fpl, arg.fpl, zeroCaseLeft));
#else
    return *this;
#endif
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
#ifdef CVC4_USE_SYMFPU
    return ((t == fp.t)
            && symfpu::smtlibEqual<symfpuLiteral::traits>(t, fpl, fp.fpl));
#else
    return ( (t == fp.t) );
#endif
  }

  bool FloatingPoint::operator <= (const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return symfpu::lessThanOrEqual<symfpuLiteral::traits>(t, fpl, arg.fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::operator < (const FloatingPoint &arg) const {
#ifdef CVC4_USE_SYMFPU
    Assert(this->t == arg.t);
    return symfpu::lessThan<symfpuLiteral::traits>(t, fpl, arg.fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isNormal (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isNormal<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isSubnormal (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isSubnormal<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isZero (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isZero<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isInfinite (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isInfinite<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isNaN (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isNaN<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isNegative (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isNegative<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  bool FloatingPoint::isPositive (void) const {
#ifdef CVC4_USE_SYMFPU
    return symfpu::isPositive<symfpuLiteral::traits>(t, fpl);
#else
    return false;
#endif
  }

  FloatingPoint FloatingPoint::convert (const FloatingPointSize &target, const RoundingMode &rm) const {
#ifdef CVC4_USE_SYMFPU
    return FloatingPoint(
        target,
        symfpu::convertFloatToFloat<symfpuLiteral::traits>(t, target, rm, fpl));
#else
    return *this;
#endif
  }
  
  BitVector FloatingPoint::convertToBVTotal (BitVectorSize width, const RoundingMode &rm, bool signedBV, BitVector undefinedCase) const {
#ifdef CVC4_USE_SYMFPU
    if (signedBV)
      return symfpu::convertFloatToSBV<symfpuLiteral::traits>(
          t, rm, fpl, width, undefinedCase);
    else
      return symfpu::convertFloatToUBV<symfpuLiteral::traits>(
          t, rm, fpl, width, undefinedCase);
#else
    return undefinedCase;
#endif
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
#ifdef CVC4_USE_SYMFPU
      Integer sign((this->fpl.getSign()) ? -1 : 1);
      Integer exp(
          this->fpl.getExponent().toSignedInteger()
          - (Integer(t.significand()
                     - 1)));  // -1 as forcibly normalised into the [1,2) range
      Integer significand(this->fpl.getSignificand().toInteger());
#else
      Integer sign(0);
      Integer exp(0);
      Integer significand(0);
#endif
      Integer signedSignificand(sign * significand);

      // We only have multiplyByPow(uint32_t) so we can't convert all numbers.
      // As we convert Integer -> unsigned int -> uint32_t we need that
      // unsigned int is not smaller than uint32_t
      static_assert(sizeof(unsigned int) >= sizeof(uint32_t),
		    "Conversion float -> real could loose data");
#ifdef CVC4_ASSERTIONS
      // Note that multipling by 2^n requires n bits of space (worst case)
      // so, in effect, these tests limit us to cases where the resultant
      // number requires up to 2^32 bits = 512 megabyte to represent.
      Integer shiftLimit(std::numeric_limits<uint32_t>::max());
#endif

      if (!(exp.strictlyNegative())) {
	Assert(exp <= shiftLimit);
	Integer r(signedSignificand.multiplyByPow2(exp.toUnsignedInt()));
	return PartialRational(Rational(r), true);
      } else {
	Integer one(1U);
	Assert((-exp) <= shiftLimit);
	Integer q(one.multiplyByPow2((-exp).toUnsignedInt()));
	Rational r(signedSignificand, q);
	return PartialRational(r, true);
      }
    }

    Unreachable() << "Convert float literal to real broken.";
  }

  BitVector FloatingPoint::pack (void) const {
#ifdef CVC4_USE_SYMFPU
    BitVector bv(symfpu::pack<symfpuLiteral::traits>(this->t, this->fpl));
#else
    BitVector bv(4u,0u);
#endif
    return bv;
  }

std::string FloatingPoint::toString(bool printAsIndexed) const
{
  std::string str;
  // retrive BV value
  BitVector bv(pack());
  unsigned largestSignificandBit =
      t.significand() - 2;  // -1 for -inclusive, -1 for hidden
  unsigned largestExponentBit =
      (t.exponent() - 1) + (largestSignificandBit + 1);
  BitVector v[3];
  v[0] = bv.extract(largestExponentBit + 1, largestExponentBit + 1);
  v[1] = bv.extract(largestExponentBit, largestSignificandBit + 1);
  v[2] = bv.extract(largestSignificandBit, 0);
  str.append("(fp ");
  for (unsigned i = 0; i < 3; ++i)
  {
    if (printAsIndexed)
    {
      str.append("(_ bv");
      str.append(v[i].getValue().toString());
      str.append(" ");
      str.append(std::to_string(v[i].getSize()));
      str.append(")");
    }
    else
    {
      str.append("#b");
      str.append(v[i].toString());
    }
    if (i < 2)
    {
      str.append(" ");
    }
  }
  str.append(")");
  return str;
}

}/* CVC4 namespace */
