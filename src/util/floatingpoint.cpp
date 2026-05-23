/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include <cmath>

#include "base/check.h"
#include "util/floatingpoint_literal.h"
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
    : d_fpl(FloatingPointLiteral::create(d_exp_size, d_sig_size, bv))
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size, const BitVector& bv)
    : d_fpl(FloatingPointLiteral::create(size, bv))
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const BitVector& bv,
                             bool signedBV)
    : d_fpl(FloatingPointLiteral::create(size, rm, bv, signedBV))
{
}

FloatingPoint::FloatingPoint(std::unique_ptr<FloatingPointLiteral>&& fpl)
    : d_fpl(std::move(fpl))
{
}

FloatingPoint::FloatingPoint(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const Rational& r)
    : d_fpl(FloatingPointLiteral::createFromRational(size, rm, r))
{
}

FloatingPoint::FloatingPoint(const FloatingPoint& fp) : d_fpl(fp.d_fpl->clone())
{
}

FloatingPoint::FloatingPoint(FloatingPoint&& fp) noexcept
    : d_fpl(std::move(fp.d_fpl))
{
}

FloatingPoint& FloatingPoint::operator=(const FloatingPoint& other)
{
  if (this != &other)
  {
    d_fpl = other.d_fpl->clone();
  }
  return *this;
}

FloatingPoint& FloatingPoint::operator=(FloatingPoint&& other) noexcept
{
  if (this != &other)
  {
    d_fpl = std::move(other.d_fpl);
  }
  return *this;
}

FloatingPoint::~FloatingPoint() {}

const FloatingPointSize& FloatingPoint::getSize() const
{
  return d_fpl->getSize();
}

FloatingPoint FloatingPoint::makeNaN(const FloatingPointSize& size)
{
  return FloatingPoint(FloatingPointLiteral::create(
      size, FloatingPointLiteral::SpecialConstKind::FPNAN));
}

FloatingPoint FloatingPoint::makeInf(const FloatingPointSize& size, bool sign)
{
  return FloatingPoint(FloatingPointLiteral::create(
      size, FloatingPointLiteral::SpecialConstKind::FPINF, sign));
}

FloatingPoint FloatingPoint::makeZero(const FloatingPointSize& size, bool sign)
{
  return FloatingPoint(FloatingPointLiteral::create(
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
  return FloatingPoint(d_fpl->absolute());
}

FloatingPoint FloatingPoint::negate(void) const
{
  return FloatingPoint(d_fpl->negate());
}

FloatingPoint FloatingPoint::add(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
  return FloatingPoint(d_fpl->add(rm, *arg.d_fpl));
}

FloatingPoint FloatingPoint::sub(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
  return FloatingPoint(d_fpl->sub(rm, *arg.d_fpl));
}

FloatingPoint FloatingPoint::mult(const RoundingMode& rm,
                                  const FloatingPoint& arg) const
{
  return FloatingPoint(d_fpl->mult(rm, *arg.d_fpl));
}

FloatingPoint FloatingPoint::fma(const RoundingMode& rm,
                                 const FloatingPoint& arg1,
                                 const FloatingPoint& arg2) const
{
  return FloatingPoint(d_fpl->fma(rm, *arg1.d_fpl, *arg2.d_fpl));
}

FloatingPoint FloatingPoint::div(const RoundingMode& rm,
                                 const FloatingPoint& arg) const
{
  return FloatingPoint(d_fpl->div(rm, *arg.d_fpl));
}

FloatingPoint FloatingPoint::sqrt(const RoundingMode& rm) const
{
  return FloatingPoint(d_fpl->sqrt(rm));
}

FloatingPoint FloatingPoint::rti(const RoundingMode& rm) const
{
  return FloatingPoint(d_fpl->rti(rm));
}

FloatingPoint FloatingPoint::rem(const FloatingPoint& arg) const
{
  return FloatingPoint(d_fpl->rem(*arg.d_fpl));
}

FloatingPoint FloatingPoint::maxTotal(const FloatingPoint& arg,
                                      bool zeroCaseLeft) const
{
  return FloatingPoint(d_fpl->maxTotal(*arg.d_fpl, zeroCaseLeft));
}

FloatingPoint FloatingPoint::minTotal(const FloatingPoint& arg,
                                      bool zeroCaseLeft) const
{
  return FloatingPoint(d_fpl->minTotal(*arg.d_fpl, zeroCaseLeft));
}

// Suppress clang-analyzer-core.uninitialized.Assign for the
// following functions as a workaround for a false positive
// in clang-tidy 18.
// NOLINTBEGIN(clang-analyzer-core.uninitialized.Assign)
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
// NOLINTEND(clang-analyzer-core.uninitialized.Assign)

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

BitVector FloatingPoint::getUnpackedExponent() const
{
  return d_fpl->getUnpackedExponent();
}

BitVector FloatingPoint::getUnpackedSignificand() const
{
  return d_fpl->getUnpackedSignificand();
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
  return FloatingPoint(d_fpl->convert(target, rm));
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
  return d_fpl->convertToRational();
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
