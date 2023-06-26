/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Haniel Barbosa
 * Copyright (c) 2013  University of Oxford
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A floating-point value.
 *
 * This file contains the data structures used by the constant and parametric
 * types of the floating point theory.
 */

#include "util/floatingpoint.h"

#include <math.h>

#include <limits>

#include "base/check.h"
#include "util/floatingpoint_literal_symfpu.h"
#include "util/integer.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

/* -------------------------------------------------------------------------- */

uint32_t FloatingPoint::getUnpackedExponentWidth(FloatingPointSize& size)
{
  return FloatingPointLiteral::getUnpackedExponentWidth(size);
}

uint32_t FloatingPoint::getUnpackedSignificandWidth(FloatingPointSize& size)
{
  return FloatingPointLiteral::getUnpackedSignificandWidth(size);
}

FloatingPoint::FloatingPoint(uint32_t d_exp_size,
                             uint32_t d_sig_size,
                             const BitVector& bv)
    : d_fpl(new FloatingPointLiteral(d_exp_size, d_sig_size, bv))
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size, const BitVector& bv)
    : d_fpl(new FloatingPointLiteral(size, bv))
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const BitVector& bv,
                             bool signedBV)
    : d_fpl(new FloatingPointLiteral(size, rm, bv, signedBV))
{
}

FloatingPoint::FloatingPoint(FloatingPointLiteral* fpl) { d_fpl.reset(fpl); }

FloatingPoint::FloatingPoint(const FloatingPoint& fp)
{
  d_fpl.reset(new FloatingPointLiteral(*fp.d_fpl));
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const Rational& r)
{
  Rational two(2, 1);

  if (r.isZero())
  {
    // In keeping with the SMT-LIB standard
    d_fpl.reset(new FloatingPointLiteral(
        size, FloatingPointLiteral::SpecialConstKind::FPZERO, false));
  }
  else
  {
    uint32_t negative = (r.sgn() < 0) ? 1 : 0;
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
        sig = sig.setBit(0, true);
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
      sig = sig.setBit(0, true);
    }

    // Build an exact float
    FloatingPointSize exactFormat(expBits, sigBits);

    // A small subtlety... if the format has expBits the unpacked format
    // may have more to allow subnormals to be normalised.
    // Thus...
    uint32_t extension =
        FloatingPointLiteral::getUnpackedExponentWidth(exactFormat) - expBits;

    FloatingPointLiteral exactFloat(
        exactFormat, negative, exactExp.signExtend(extension), sig);

    // Then cast...
    d_fpl.reset(new FloatingPointLiteral(exactFloat.convert(size, rm)));
  }
}

FloatingPoint::~FloatingPoint()
{
}

const FloatingPointSize& FloatingPoint::getSize() const
{
  return d_fpl->getSize();
}

FloatingPoint FloatingPoint::makeNaN(const FloatingPointSize& size)
{
  return FloatingPoint(new FloatingPointLiteral(
      size, FloatingPointLiteral::SpecialConstKind::FPNAN));
}

FloatingPoint FloatingPoint::makeInf(const FloatingPointSize& size, bool sign)
{
  return FloatingPoint(new FloatingPointLiteral(
      size, FloatingPointLiteral::SpecialConstKind::FPINF, sign));
}

FloatingPoint FloatingPoint::makeZero(const FloatingPointSize& size, bool sign)
{
  return FloatingPoint(new FloatingPointLiteral(
      size, FloatingPointLiteral::SpecialConstKind::FPZERO, sign));
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
  BitVector bvexp = BitVector::mkOnes(size.packedExponentWidth());
  bvexp.setBit(0, false);
  BitVector bvsig = BitVector::mkOnes(size.packedSignificandWidth());
  return FloatingPoint(size, bvsign.concat(bvexp).concat(bvsig));
}

FloatingPoint FloatingPoint::absolute(void) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->absolute()));
}

FloatingPoint FloatingPoint::negate(void) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->negate()));
}

FloatingPoint FloatingPoint::add(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->add(rm, *arg.d_fpl)));
}

FloatingPoint FloatingPoint::sub(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->sub(rm, *arg.d_fpl)));
}

FloatingPoint FloatingPoint::mult(const RoundingMode& rm,
                                  const FloatingPoint& arg) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->mult(rm, *arg.d_fpl)));
}

FloatingPoint FloatingPoint::fma(const RoundingMode& rm,
                                 const FloatingPoint& arg1,
                                 const FloatingPoint& arg2) const
{
  return FloatingPoint(
      new FloatingPointLiteral(d_fpl->fma(rm, *arg1.d_fpl, *arg2.d_fpl)));
}

FloatingPoint FloatingPoint::div(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->div(rm, *arg.d_fpl)));
}

FloatingPoint FloatingPoint::sqrt(const RoundingMode& rm) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->sqrt(rm)));
}

FloatingPoint FloatingPoint::rti(const RoundingMode& rm) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->rti(rm)));
}

FloatingPoint FloatingPoint::rem(const FloatingPoint& arg) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->rem(*arg.d_fpl)));
}

FloatingPoint FloatingPoint::maxTotal(const FloatingPoint& arg,
                                      bool zeroCaseLeft) const
{
  return FloatingPoint(
      new FloatingPointLiteral(d_fpl->maxTotal(*arg.d_fpl, zeroCaseLeft)));
}

FloatingPoint FloatingPoint::minTotal(const FloatingPoint& arg,
                                      bool zeroCaseLeft) const
{
  return FloatingPoint(
      new FloatingPointLiteral(d_fpl->minTotal(*arg.d_fpl, zeroCaseLeft)));
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
  return *d_fpl == *fp.d_fpl;
}

bool FloatingPoint::operator<=(const FloatingPoint& fp) const
{
  return *d_fpl <= *fp.d_fpl;
}

bool FloatingPoint::operator<(const FloatingPoint& fp) const
{
  return *d_fpl < *fp.d_fpl;
}

BitVector FloatingPoint::getExponent() const { return d_fpl->getExponent(); }

BitVector FloatingPoint::getSignificand() const
{
  return d_fpl->getSignificand();
}

bool FloatingPoint::getSign() const { return d_fpl->getSign(); }

bool FloatingPoint::isNormal(void) const { return d_fpl->isNormal(); }

bool FloatingPoint::isSubnormal(void) const { return d_fpl->isSubnormal(); }

bool FloatingPoint::isZero(void) const { return d_fpl->isZero(); }

bool FloatingPoint::isInfinite(void) const { return d_fpl->isInfinite(); }

bool FloatingPoint::isNaN(void) const { return d_fpl->isNaN(); }

bool FloatingPoint::isNegative(void) const { return d_fpl->isNegative(); }

bool FloatingPoint::isPositive(void) const { return d_fpl->isPositive(); }

FloatingPoint FloatingPoint::convert(const FloatingPointSize& target,
                                     const RoundingMode& rm) const
{
  return FloatingPoint(new FloatingPointLiteral(d_fpl->convert(target, rm)));
}

BitVector FloatingPoint::convertToBVTotal(BitVectorSize width,
                                          const RoundingMode& rm,
                                          bool signedBV,
                                          BitVector undefinedCase) const
{
  if (signedBV)
  {
    return d_fpl->convertToSBVTotal(width, rm, undefinedCase);
  }
  return d_fpl->convertToUBVTotal(width, rm, undefinedCase);
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
  Integer sign((d_fpl->getSign()) ? -1 : 1);
  Integer exp(
      d_fpl->getExponent().toSignedInteger()
      - (Integer(d_fpl->getSize().significandWidth()
                 - 1)));  // -1 as forcibly normalised into the [1,2) range
  Integer significand(d_fpl->getSignificand().toInteger());
  Integer signedSignificand(sign * significand);

  // We only have multiplyByPow(uint32_t) so we can't convert all numbers.
  // As we convert Integer -> unsigned int -> uint32_t we need that
  // unsigned int is not smaller than uint32_t
  static_assert(sizeof(unsigned int) >= sizeof(uint32_t),
                "Conversion float -> real could loose data");
#ifdef CVC5_ASSERTIONS
  // Note that multipling by 2^n requires n bits of space (worst case)
  // so, in effect, these tests limit us to cases where the resultant
  // number requires up to 2^32 bits = 512 megabyte to represent.
  Integer shiftLimit(std::numeric_limits<uint32_t>::max());
#endif

  if (!(exp.strictlyNegative()))
  {
    Assert(exp <= shiftLimit);
    Integer r(signedSignificand.multiplyByPow2(exp.toUnsignedInt()));
    return PartialRational(Rational(r), true);
  }
  Integer one(1U);
  Assert((-exp) <= shiftLimit);
  Integer q(one.multiplyByPow2((-exp).toUnsignedInt()));
  Rational r(signedSignificand, q);
  return PartialRational(r, true);
}

BitVector FloatingPoint::pack(void) const { return d_fpl->pack(); }

void FloatingPoint::getIEEEBitvectors(BitVector& sign,
                                      BitVector& exp,
                                      BitVector& sig) const
{
  // retrieve BV value
  BitVector bv(pack());
  uint32_t largestSignificandBit =
      getSize().significandWidth() - 2;  // -1 for -inclusive, -1 for hidden
  uint32_t largestExponentBit =
      (getSize().exponentWidth() - 1) + (largestSignificandBit + 1);
  sign = bv.extract(largestExponentBit + 1, largestExponentBit + 1);
  exp = bv.extract(largestExponentBit, largestSignificandBit + 1);
  sig = bv.extract(largestSignificandBit, 0);
}

std::string FloatingPoint::toString(bool printAsIndexed) const
{
  std::string str;
  // retrive BV value
  BitVector v[3];
  getIEEEBitvectors(v[0], v[1], v[2]);
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
  return os << "(_ to_fp " << fpcs.getSize().exponentWidth() << " "
            << fpcs.getSize().significandWidth() << ")";
}
}  // namespace cvc5::internal
