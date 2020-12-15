/*********************                                                        */
/*! \file floatingpoint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Martin Brain, Haniel Barbosa
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A floating-point value.
 **
 ** This file contains the data structures used by the constant and parametric
 ** types of the floating point theory.
 **/

#include "util/floatingpoint.h"

#include <math.h>

#include <limits>

#include "base/check.h"
#include "util/floatingpoint_literal_symfpu.h"
#include "util/integer.h"

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

/* -------------------------------------------------------------------------- */

#ifdef CVC4_USE_SYMFPU
namespace symfpu {

#define CVC4_LIT_ITE_DFN(T)                                            \
  template <>                                                          \
  struct ite<::CVC4::symfpuLiteral::CVC4Prop, T>                       \
  {                                                                    \
    static const T& iteOp(const ::CVC4::symfpuLiteral::CVC4Prop& cond, \
                          const T& l,                                  \
                          const T& r)                                  \
    {                                                                  \
      return cond ? l : r;                                             \
    }                                                                  \
  }

CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::rm);
CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::prop);
CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::sbv);
CVC4_LIT_ITE_DFN(::CVC4::symfpuLiteral::traits::ubv);

#undef CVC4_LIT_ITE_DFN
}
#endif

/* -------------------------------------------------------------------------- */

namespace CVC4 {

/* -------------------------------------------------------------------------- */

uint32_t FloatingPoint::getUnpackedExponentWidth(FloatingPointSize& size)
{
#ifdef CVC4_USE_SYMFPU
  return SymFPUUnpackedFloatLiteral::exponentWidth(size);
#else
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return 2;
#endif
}

uint32_t FloatingPoint::getUnpackedSignificandWidth(FloatingPointSize& size)
{
#ifdef CVC4_USE_SYMFPU
  return SymFPUUnpackedFloatLiteral::significandWidth(size);
#else
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return 2;
#endif
}

FloatingPoint::FloatingPoint(uint32_t d_exp_size,
                             uint32_t d_sig_size,
                             const BitVector& bv)
    : d_fp_size(d_exp_size, d_sig_size),
#ifdef CVC4_USE_SYMFPU
      d_fpl(new FloatingPointLiteral(symfpu::unpack<symfpuLiteral::traits>(
          symfpuLiteral::CVC4FPSize(d_exp_size, d_sig_size), bv)))
#else
      d_fpl(new FloatingPointLiteral(d_exp_size, d_sig_size, 0.0))
#endif
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size, const BitVector& bv)
    : d_fp_size(size),
#ifdef CVC4_USE_SYMFPU
      d_fpl(new FloatingPointLiteral(
          symfpu::unpack<symfpuLiteral::traits>(size, bv)))
#else
      d_fpl(new FloatingPointLiteral(
          size.exponentWidth(), size.significandWidth(), 0.0))
#endif
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const BitVector& bv,
                             bool signedBV)
    : d_fp_size(size)
{
#ifdef CVC4_USE_SYMFPU
  if (signedBV)
  {
    d_fpl.reset(new FloatingPointLiteral(
        symfpu::convertSBVToFloat<symfpuLiteral::traits>(
            symfpuLiteral::CVC4FPSize(size),
            symfpuLiteral::CVC4RM(rm),
            symfpuLiteral::CVC4SignedBitVector(bv))));
  }
  else
  {
    d_fpl.reset(new FloatingPointLiteral(
        symfpu::convertUBVToFloat<symfpuLiteral::traits>(
            symfpuLiteral::CVC4FPSize(size),
            symfpuLiteral::CVC4RM(rm),
            symfpuLiteral::CVC4UnsignedBitVector(bv))));
  }
#else
  d_fpl.reset(new FloatingPointLiteral(2, 2, 0.0));
#endif
}

FloatingPoint::FloatingPoint(const FloatingPointSize& fp_size,
                             FloatingPointLiteral* fpl)
    : d_fp_size(fp_size)
{
  d_fpl.reset(fpl);
}

FloatingPoint::FloatingPoint(const FloatingPoint& fp) : d_fp_size(fp.d_fp_size)
{
  d_fpl.reset(new FloatingPointLiteral(*fp.d_fpl));
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const Rational& r)
    : d_fp_size(size)
{
  Rational two(2, 1);

  if (r.isZero())
  {
#ifdef CVC4_USE_SYMFPU
    // In keeping with the SMT-LIB standard
    d_fpl.reset(new FloatingPointLiteral(
        SymFPUUnpackedFloatLiteral::makeZero(size, false)));
#else
    d_fpl.reset(new FloatingPointLiteral(2, 2, 0.0));
#endif
  }
  else
  {
#ifdef CVC4_USE_SYMFPU
    uint32_t negative = (r.sgn() < 0) ? 1 : 0;
#endif
    Rational rabs(r.abs());

    // Compute the exponent
    Integer exp(0U);
    Integer inc(1U);
    Rational working(1, 1);

    if (rabs != working)
    {
      if (rabs < working)
      {
        while (rabs < working)
        {
          exp -= inc;
          working /= two;
        }
      }
      else
      {
        while (rabs >= working)
        {
          exp += inc;
          working *= two;
        }
        exp -= inc;
        working /= two;
      }
    }

    Assert(working <= rabs);
    Assert(rabs < working * two);

    // Work out the number of bits required to represent the exponent for a
    // normal number
    uint32_t expBits = 2;  // No point starting with an invalid amount

    Integer doubleInt(2);
    if (exp.strictlyPositive())
    {
      // 1 more than exactly representable with expBits
      Integer representable(4);
      while (representable <= exp)
      {  // hence <=
        representable *= doubleInt;
        ++expBits;
      }
    }
    else if (exp.strictlyNegative())
    {
      Integer representable(-4);  // Exactly representable with expBits + sign
                                  // but -2^n and -(2^n - 1) are both subnormal
      while ((representable + doubleInt) > exp)
      {
        representable *= doubleInt;
        ++expBits;
      }
    }
    ++expBits;  // To allow for sign

    BitVector exactExp(expBits, exp);

    // Compute the significand.
    uint32_t sigBits = size.significandWidth() + 2;  // guard and sticky bits
    BitVector sig(sigBits, 0U);
    BitVector one(sigBits, 1U);
    Rational workingSig(0, 1);
    for (uint32_t i = 0; i < sigBits - 1; ++i)
    {
      Rational mid(workingSig + working);

      if (mid <= rabs)
      {
        sig = sig | one;
        workingSig = mid;
      }

      sig = sig.leftShift(one);
      working /= two;
    }

    // Compute the sticky bit
    Rational remainder(rabs - workingSig);
    Assert(Rational(0, 1) <= remainder);

    if (!remainder.isZero())
    {
      sig = sig | one;
    }

    // Build an exact float
    FloatingPointSize exactFormat(expBits, sigBits);

    // A small subtlety... if the format has expBits the unpacked format
    // may have more to allow subnormals to be normalised.
    // Thus...
#ifdef CVC4_USE_SYMFPU
    uint32_t extension =
        SymFPUUnpackedFloatLiteral::exponentWidth(exactFormat) - expBits;

    FloatingPointLiteral exactFloat(
        negative, exactExp.signExtend(extension), sig);

    // Then cast...
    d_fpl.reset(new FloatingPointLiteral(symfpu::convertFloatToFloat(
        exactFormat, size, rm, exactFloat.d_symuf)));
#else
    Unreachable() << "no concrete implementation of FloatingPointLiteral";
#endif
  }
}

FloatingPoint::~FloatingPoint()
{
}

FloatingPoint FloatingPoint::makeNaN(const FloatingPointSize& size)
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(
      size,
      new FloatingPointLiteral(SymFPUUnpackedFloatLiteral::makeNaN(size)));
#else
  return FloatingPoint(2, 2, BitVector(4U, 0U));
#endif
}

FloatingPoint FloatingPoint::makeInf(const FloatingPointSize& size, bool sign)
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(size,
                       new FloatingPointLiteral(
                           SymFPUUnpackedFloatLiteral::makeInf(size, sign)));
#else
  return FloatingPoint(2, 2, BitVector(4U, 0U));
#endif
}

FloatingPoint FloatingPoint::makeZero(const FloatingPointSize& size, bool sign)
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(size,
                       new FloatingPointLiteral(
                           SymFPUUnpackedFloatLiteral::makeZero(size, sign)));
#else
  return FloatingPoint(2, 2, BitVector(4U, 0U));
#endif
}

FloatingPoint FloatingPoint::makeMinSubnormal(const FloatingPointSize& size,
                                              bool sign)
{
  BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
  BitVector bvexp = BitVector::mkZero(size.packedExponentWidth());
  BitVector bvsig = BitVector::mkOne(size.packedSignificandWidth());
  return FloatingPoint(size, bvsign.concat(bvexp).concat(bvsig));
}

FloatingPoint FloatingPoint::makeMaxSubnormal(const FloatingPointSize& size,
                                              bool sign)
{
  BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
  BitVector bvexp = BitVector::mkZero(size.packedExponentWidth());
  BitVector bvsig = BitVector::mkOnes(size.packedSignificandWidth());
  return FloatingPoint(size, bvsign.concat(bvexp).concat(bvsig));
}

FloatingPoint FloatingPoint::makeMinNormal(const FloatingPointSize& size,
                                           bool sign)
{
  BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
  BitVector bvexp = BitVector::mkOne(size.packedExponentWidth());
  BitVector bvsig = BitVector::mkZero(size.packedSignificandWidth());
  return FloatingPoint(size, bvsign.concat(bvexp).concat(bvsig));
}

FloatingPoint FloatingPoint::makeMaxNormal(const FloatingPointSize& size,
                                           bool sign)
{
  BitVector bvsign = sign ? BitVector::mkOne(1) : BitVector::mkZero(1);
  BitVector bvexp =
      BitVector::mkOnes(size.packedExponentWidth()).setBit(0, false);
  BitVector bvsig = BitVector::mkOnes(size.packedSignificandWidth());
  return FloatingPoint(size, bvsign.concat(bvexp).concat(bvsig));
}

/* Operations implemented using symfpu */
FloatingPoint FloatingPoint::absolute(void) const
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(
          symfpu::absolute<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::negate(void) const
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(
          symfpu::negate<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::plus(const RoundingMode& rm,
                                  const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::add<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf, arg.d_fpl->d_symuf, true)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::sub(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::add<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf, arg.d_fpl->d_symuf, false)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::mult(const RoundingMode& rm,
                                  const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::multiply<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf, arg.d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::fma(const RoundingMode& rm,
                                 const FloatingPoint& arg1,
                                 const FloatingPoint& arg2) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg1.d_fp_size);
  Assert(d_fp_size == arg2.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(
          symfpu::fma<symfpuLiteral::traits>(d_fp_size,
                                             rm,
                                             d_fpl->d_symuf,
                                             arg1.d_fpl->d_symuf,
                                             arg2.d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::div(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::divide<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf, arg.d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::sqrt(const RoundingMode& rm) const
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(
          symfpu::sqrt<symfpuLiteral::traits>(d_fp_size, rm, d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::rti(const RoundingMode& rm) const
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::roundToIntegral<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::rem(const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::remainder<symfpuLiteral::traits>(
          d_fp_size, d_fpl->d_symuf, arg.d_fpl->d_symuf)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::maxTotal(const FloatingPoint& arg,
                                      bool zeroCaseLeft) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::max<symfpuLiteral::traits>(
          d_fp_size, d_fpl->d_symuf, arg.d_fpl->d_symuf, zeroCaseLeft)));
#else
  return *this;
#endif
}

FloatingPoint FloatingPoint::minTotal(const FloatingPoint& arg,
                                      bool zeroCaseLeft) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPoint(
      d_fp_size,
      new FloatingPointLiteral(symfpu::min<symfpuLiteral::traits>(
          d_fp_size, d_fpl->d_symuf, arg.d_fpl->d_symuf, zeroCaseLeft)));
#else
  return *this;
#endif
}

FloatingPoint::PartialFloatingPoint FloatingPoint::max(
    const FloatingPoint& arg) const
{
  FloatingPoint tmp(maxTotal(arg, true));
  return PartialFloatingPoint(tmp, tmp == maxTotal(arg, false));
}

FloatingPoint::PartialFloatingPoint FloatingPoint::min(
    const FloatingPoint& arg) const
{
  FloatingPoint tmp(minTotal(arg, true));
  return PartialFloatingPoint(tmp, tmp == minTotal(arg, false));
}

bool FloatingPoint::operator==(const FloatingPoint& fp) const
{
#ifdef CVC4_USE_SYMFPU
  return ((d_fp_size == fp.d_fp_size)
          && symfpu::smtlibEqual<symfpuLiteral::traits>(
              d_fp_size, d_fpl->d_symuf, fp.d_fpl->d_symuf));
#else
  return ((d_fp_size == fp.d_fp_size));
#endif
}

bool FloatingPoint::operator<=(const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return symfpu::lessThanOrEqual<symfpuLiteral::traits>(
      d_fp_size, d_fpl->d_symuf, arg.d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::operator<(const FloatingPoint& arg) const
{
#ifdef CVC4_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return symfpu::lessThan<symfpuLiteral::traits>(
      d_fp_size, d_fpl->d_symuf, arg.d_fpl->d_symuf);
#else
  return false;
#endif
}

BitVector FloatingPoint::getExponent() const
{
#ifdef CVC4_USE_SYMFPU
  return d_fpl->d_symuf.exponent;
#else
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return BitVector();
#endif
}

BitVector FloatingPoint::getSignificand() const
{
#ifdef CVC4_USE_SYMFPU
  return d_fpl->d_symuf.significand;
#else
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return BitVector();
#endif
}

bool FloatingPoint::getSign() const
{
#ifdef CVC4_USE_SYMFPU
  return d_fpl->d_symuf.sign;
#else
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return false;
#endif
}

bool FloatingPoint::isNormal(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isNormal<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::isSubnormal(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isSubnormal<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::isZero(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isZero<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::isInfinite(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isInfinite<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::isNaN(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isNaN<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::isNegative(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isNegative<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

bool FloatingPoint::isPositive(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isPositive<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf);
#else
  return false;
#endif
}

FloatingPoint FloatingPoint::convert(const FloatingPointSize& target,
                                     const RoundingMode& rm) const
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPoint(target,
                       new FloatingPointLiteral(
                           symfpu::convertFloatToFloat<symfpuLiteral::traits>(
                               d_fp_size, target, rm, d_fpl->d_symuf)));
#else
  return *this;
#endif
}

BitVector FloatingPoint::convertToBVTotal(BitVectorSize width,
                                          const RoundingMode& rm,
                                          bool signedBV,
                                          BitVector undefinedCase) const
{
#ifdef CVC4_USE_SYMFPU
    if (signedBV)
      return symfpu::convertFloatToSBV<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf, width, undefinedCase);
    else
      return symfpu::convertFloatToUBV<symfpuLiteral::traits>(
          d_fp_size, rm, d_fpl->d_symuf, width, undefinedCase);
#else
  return undefinedCase;
#endif
}

Rational FloatingPoint::convertToRationalTotal(Rational undefinedCase) const
{
  PartialRational p(convertToRational());

  return p.second ? p.first : undefinedCase;
}

FloatingPoint::PartialBitVector FloatingPoint::convertToBV(
    BitVectorSize width, const RoundingMode& rm, bool signedBV) const
{
  BitVector tmp(convertToBVTotal(width, rm, signedBV, BitVector(width, 0U)));
  BitVector confirm(
      convertToBVTotal(width, rm, signedBV, BitVector(width, 1U)));

  return PartialBitVector(tmp, tmp == confirm);
}

FloatingPoint::PartialRational FloatingPoint::convertToRational(void) const
{
  if (isNaN() || isInfinite())
  {
    return PartialRational(Rational(0U, 1U), false);
  }
  if (isZero())
  {
    return PartialRational(Rational(0U, 1U), true);
  }
  else
  {
#ifdef CVC4_USE_SYMFPU
    Integer sign((d_fpl->d_symuf.getSign()) ? -1 : 1);
    Integer exp(
        d_fpl->d_symuf.getExponent().toSignedInteger()
        - (Integer(d_fp_size.significandWidth()
                   - 1)));  // -1 as forcibly normalised into the [1,2) range
    Integer significand(d_fpl->d_symuf.getSignificand().toInteger());
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

BitVector FloatingPoint::pack(void) const
{
#ifdef CVC4_USE_SYMFPU
  BitVector bv(symfpu::pack<symfpuLiteral::traits>(d_fp_size, d_fpl->d_symuf));
#else
  BitVector bv(4u, 0u);
#endif
  return bv;
}

std::string FloatingPoint::toString(bool printAsIndexed) const
{
  std::string str;
  // retrive BV value
  BitVector bv(pack());
  uint32_t largestSignificandBit =
      d_fp_size.significandWidth() - 2;  // -1 for -inclusive, -1 for hidden
  uint32_t largestExponentBit =
      (d_fp_size.exponentWidth() - 1) + (largestSignificandBit + 1);
  BitVector v[3];
  v[0] = bv.extract(largestExponentBit + 1, largestExponentBit + 1);
  v[1] = bv.extract(largestExponentBit, largestSignificandBit + 1);
  v[2] = bv.extract(largestSignificandBit, 0);
  str.append("(fp ");
  for (uint32_t i = 0; i < 3; ++i)
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

std::ostream& operator<<(std::ostream& os, const FloatingPoint& fp)
{
  // print in binary notation
  return os << fp.toString();
}

std::ostream& operator<<(std::ostream& os, const FloatingPointSize& fps)
{
  return os << "(_ FloatingPoint " << fps.exponentWidth() << " "
            << fps.significandWidth() << ")";
}

std::ostream& operator<<(std::ostream& os, const FloatingPointConvertSort& fpcs)
{
  return os << "(_ to_fp " << fpcs.d_fp_size.exponentWidth() << " "
            << fpcs.d_fp_size.significandWidth() << ")";
}
}/* CVC4 namespace */
