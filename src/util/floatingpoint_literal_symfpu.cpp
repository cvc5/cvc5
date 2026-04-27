/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SymFPU glue code for floating-point values.
 */
#include "util/floatingpoint_literal_symfpu.h"

#include <limits>

#include "base/check.h"
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
#include "util/floatingpoint_literal.h"
#include "util/rational.h"

/* -------------------------------------------------------------------------- */

namespace symfpu {

#define CVC5_LIT_ITE_DFN(T)                                                    \
  template <>                                                                  \
  struct ite<cvc5::internal::symfpuLiteral::Cvc5Prop, T>                       \
  {                                                                            \
    static const T& iteOp(const cvc5::internal::symfpuLiteral::Cvc5Prop& cond, \
                          const T& l,                                          \
                          const T& r)                                          \
    {                                                                          \
      return cond ? l : r;                                                     \
    }                                                                          \
  }

CVC5_LIT_ITE_DFN(cvc5::internal::symfpuLiteral::traits::rm);
CVC5_LIT_ITE_DFN(cvc5::internal::symfpuLiteral::traits::prop);
CVC5_LIT_ITE_DFN(cvc5::internal::symfpuLiteral::traits::sbv);
CVC5_LIT_ITE_DFN(cvc5::internal::symfpuLiteral::traits::ubv);

#undef CVC5_LIT_ITE_DFN
}  // namespace symfpu

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

/* -------------------------------------------------------------------------- */

namespace {
const FloatingPointLiteralSymFPU& asSymFPU(const FloatingPointLiteral& lit)
{
  Assert(dynamic_cast<const FloatingPointLiteralSymFPU*>(&lit) != nullptr);
  return static_cast<const FloatingPointLiteralSymFPU&>(lit);
}
}  // namespace

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(uint32_t exp_size,
                                                       uint32_t sig_size,
                                                       const BitVector& bv)
    : FloatingPointLiteral(exp_size, sig_size),
      d_symuf(
          new SymFPUUnpackedFloatLiteral(symfpu::unpack<symfpuLiteral::traits>(
              symfpuLiteral::Cvc5FPSize(exp_size, sig_size), bv)))
{
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size,
    CVC5_UNUSED FloatingPointLiteralSymFPU::SpecialConstKind kind)
    : FloatingPointLiteral(size),
      d_symuf(new SymFPUUnpackedFloatLiteral(
          SymFPUUnpackedFloatLiteral::makeNaN(size)))
{
  Assert(kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPNAN);
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size,
    FloatingPointLiteralSymFPU::SpecialConstKind kind,
    bool sign)
    : FloatingPointLiteral(size),
      d_symuf(new SymFPUUnpackedFloatLiteral(
          kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPINF
              ? SymFPUUnpackedFloatLiteral::makeInf(size, sign)
              : SymFPUUnpackedFloatLiteral::makeZero(size, sign)))
{
  Assert(kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPINF
         || kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPZERO);
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size, const BitVector& bv)
    : FloatingPointLiteral(size),
      d_symuf(new SymFPUUnpackedFloatLiteral(
          symfpu::unpack<symfpuLiteral::traits>(size, bv)))
{
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size,
    const RoundingMode& rm,
    const BitVector& bv,
    bool signedBV)
    : FloatingPointLiteral(size)
{
  if (signedBV)
  {
    if (bv.getSize() == 1)
    {
      SymFPUUnpackedFloatLiteral uf =
          symfpu::convertUBVToFloat<symfpuLiteral::traits>(size, rm, bv);
      /* We need special handling for bit-vectors of size one since symFPU does
       * not allow conversions from signed bit-vectors of size one.  */
      if (bv.is_one())
      {
        d_symuf.reset(new SymFPUUnpackedFloatLiteral(
            symfpu::negate<symfpuLiteral::traits>(size, uf)));
      }
      else
      {
        d_symuf.reset(new SymFPUUnpackedFloatLiteral(uf));
      }
    }
    else
    {
      d_symuf.reset(new SymFPUUnpackedFloatLiteral(
          symfpu::convertSBVToFloat<symfpuLiteral::traits>(size, rm, bv)));
    }
  }
  else
  {
    d_symuf.reset(new SymFPUUnpackedFloatLiteral(
        symfpu::convertUBVToFloat<symfpuLiteral::traits>(size, rm, bv)));
  }
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointLiteralSymFPU& other)
    : FloatingPointLiteral(other.getSize()),
      d_symuf(new SymFPUUnpackedFloatLiteral(*other.d_symuf))
{
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    FloatingPointLiteralSymFPU&& other) noexcept
    : FloatingPointLiteral(other.getSize()), d_symuf(std::move(other.d_symuf))
{
}

FloatingPointLiteralSymFPU& FloatingPointLiteralSymFPU::operator=(
    const FloatingPointLiteralSymFPU& other)
{
  if (this != &other)
  {
    d_fp_size = other.d_fp_size;
    d_symuf.reset(new SymFPUUnpackedFloatLiteral(*other.d_symuf));
  }
  return *this;
}

FloatingPointLiteralSymFPU& FloatingPointLiteralSymFPU::operator=(
    FloatingPointLiteralSymFPU&& other) noexcept
{
  if (this != &other)
  {
    d_fp_size = other.d_fp_size;
    d_symuf = std::move(other.d_symuf);
  }
  return *this;
}

FloatingPointLiteralSymFPU::~FloatingPointLiteralSymFPU() {}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::fromUnpacked(
    const FloatingPointSize& size,
    bool sign,
    const BitVector& exp,
    const BitVector& sig)
{
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralSymFPU(size, sign, exp, sig));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::fromRational(
    const FloatingPointSize& size, const RoundingMode& rm, const Rational& r)
{
  Rational two(2, 1);

  if (r.isZero())
  {
    // In keeping with the SMT-LIB standard
    return std::unique_ptr<FloatingPointLiteral>(
        new FloatingPointLiteralSymFPU(size, SpecialConstKind::FPZERO, false));
  }

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
      SymFPUUnpackedFloatLiteral::exponentWidth(exactFormat) - expBits;

  auto exactFloat =
      fromUnpacked(exactFormat, negative, exactExp.signExtend(extension), sig);

  // Then cast...
  return exactFloat->convert(size, rm);
}

/* -------------------------------------------------------------------------- */
/* FloatingPointLiteral interface                                             */
/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::clone() const
{
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralSymFPU(*this));
}

BitVector FloatingPointLiteralSymFPU::pack(void) const
{
  BitVector bv(symfpu::pack<symfpuLiteral::traits>(d_fp_size, *d_symuf));
  return bv;
}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::absolute()
    const
{
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size, symfpu::absolute<symfpuLiteral::traits>(d_fp_size, *d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::negate() const
{
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size, symfpu::negate<symfpuLiteral::traits>(d_fp_size, *d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::add(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::add<symfpuLiteral::traits>(
          d_fp_size, rm, *d_symuf, *a.d_symuf, true)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::sub(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::add<symfpuLiteral::traits>(
          d_fp_size, rm, *d_symuf, *a.d_symuf, false)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::mult(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralSymFPU(d_fp_size,
                                     symfpu::multiply<symfpuLiteral::traits>(
                                         d_fp_size, rm, *d_symuf, *a.d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::div(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralSymFPU(d_fp_size,
                                     symfpu::divide<symfpuLiteral::traits>(
                                         d_fp_size, rm, *d_symuf, *a.d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::fma(
    const RoundingMode& rm,
    const FloatingPointLiteral& arg1,
    const FloatingPointLiteral& arg2) const
{
  const auto& a1 = asSymFPU(arg1);
  const auto& a2 = asSymFPU(arg2);
  Assert(d_fp_size == a1.d_fp_size);
  Assert(d_fp_size == a2.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::fma<symfpuLiteral::traits>(
          d_fp_size, rm, *d_symuf, *a1.d_symuf, *a2.d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::sqrt(
    const RoundingMode& rm) const
{
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size, symfpu::sqrt<symfpuLiteral::traits>(d_fp_size, rm, *d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::rti(
    const RoundingMode& rm) const
{
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::roundToIntegral<symfpuLiteral::traits>(d_fp_size, rm, *d_symuf)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::rem(
    const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(
      new FloatingPointLiteralSymFPU(d_fp_size,
                                     symfpu::remainder<symfpuLiteral::traits>(
                                         d_fp_size, *d_symuf, *a.d_symuf)));
}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::maxTotal(
    const FloatingPointLiteral& arg, bool zeroCaseLeft) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::max<symfpuLiteral::traits>(
          d_fp_size, *d_symuf, *a.d_symuf, zeroCaseLeft)));
}

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::minTotal(
    const FloatingPointLiteral& arg, bool zeroCaseLeft) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::min<symfpuLiteral::traits>(
          d_fp_size, *d_symuf, *a.d_symuf, zeroCaseLeft)));
}

/* -------------------------------------------------------------------------- */

bool FloatingPointLiteralSymFPU::operator==(
    const FloatingPointLiteral& fp) const
{
  const auto& other = asSymFPU(fp);
  return ((d_fp_size == other.d_fp_size)
          && symfpu::smtlibEqual<symfpuLiteral::traits>(
              d_fp_size, *d_symuf, *other.d_symuf));
}

bool FloatingPointLiteralSymFPU::operator<=(
    const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return symfpu::lessThanOrEqual<symfpuLiteral::traits>(
      d_fp_size, *d_symuf, *a.d_symuf);
}

bool FloatingPointLiteralSymFPU::operator<(
    const FloatingPointLiteral& arg) const
{
  const auto& a = asSymFPU(arg);
  Assert(d_fp_size == a.d_fp_size);
  return symfpu::lessThan<symfpuLiteral::traits>(
      d_fp_size, *d_symuf, *a.d_symuf);
}

/* -------------------------------------------------------------------------- */

BitVector FloatingPointLiteralSymFPU::getUnpackedExponent() const
{
  return d_symuf->exponent;
}

BitVector FloatingPointLiteralSymFPU::getUnpackedSignificand() const
{
  return d_symuf->significand;
}

bool FloatingPointLiteralSymFPU::getSign() const { return d_symuf->sign; }

/* -------------------------------------------------------------------------- */

bool FloatingPointLiteralSymFPU::isNormal(void) const
{
  return symfpu::isNormal<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

bool FloatingPointLiteralSymFPU::isSubnormal(void) const
{
  return symfpu::isSubnormal<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

bool FloatingPointLiteralSymFPU::isZero(void) const
{
  return symfpu::isZero<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

bool FloatingPointLiteralSymFPU::isInfinite(void) const
{
  return symfpu::isInfinite<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

bool FloatingPointLiteralSymFPU::isNaN(void) const
{
  return symfpu::isNaN<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

bool FloatingPointLiteralSymFPU::isNegative(void) const
{
  return symfpu::isNegative<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

bool FloatingPointLiteralSymFPU::isPositive(void) const
{
  return symfpu::isPositive<symfpuLiteral::traits>(d_fp_size, *d_symuf);
}

/* -------------------------------------------------------------------------- */

std::unique_ptr<FloatingPointLiteral> FloatingPointLiteralSymFPU::convert(
    const FloatingPointSize& target, const RoundingMode& rm) const
{
  return std::unique_ptr<FloatingPointLiteral>(new FloatingPointLiteralSymFPU(
      target,
      symfpu::convertFloatToFloat<symfpuLiteral::traits>(
          d_fp_size, target, rm, *d_symuf)));
}

BitVector FloatingPointLiteralSymFPU::convertToSBVTotal(
    BitVectorSize width, const RoundingMode& rm, BitVector undefinedCase) const
{
  return symfpu::convertFloatToSBV<symfpuLiteral::traits>(
      d_fp_size, rm, *d_symuf, width, undefinedCase);
}

BitVector FloatingPointLiteralSymFPU::convertToUBVTotal(
    BitVectorSize width, const RoundingMode& rm, BitVector undefinedCase) const
{
  return symfpu::convertFloatToUBV<symfpuLiteral::traits>(
      d_fp_size, rm, *d_symuf, width, undefinedCase);
}

std::pair<Rational, bool> FloatingPointLiteralSymFPU::convertToRational() const
{
  if (isNaN() || isInfinite())
  {
    return std::make_pair(Rational(0U, 1U), false);
  }
  if (isZero())
  {
    return std::make_pair(Rational(0U, 1U), true);
  }
  Integer sign(d_symuf->sign ? -1 : 1);
  Integer exp(
      d_symuf->exponent.toSignedInteger()
      - (Integer(d_fp_size.significandWidth()
                 - 1)));  // -1 as forcibly normalised into the [1,2) range
  Integer significand(d_symuf->significand.toInteger());
  Integer signedSignificand(sign * significand);

  // We only have multiplyByPow(uint32_t) so we can't convert all numbers.
  // As we convert Integer -> unsigned int -> uint32_t we need that
  // unsigned int is not smaller than uint32_t
  static_assert(sizeof(unsigned int) >= sizeof(uint32_t),
                "Conversion float -> real could lose data");
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
    return std::make_pair(Rational(r), true);
  }
  Integer one(1U);
  Assert((-exp) <= shiftLimit);
  Integer q(one.multiplyByPow2((-exp).toUnsignedInt()));
  Rational r(signedSignificand, q);
  return std::make_pair(r, true);
}

/* -------------------------------------------------------------------------- */
}  // namespace cvc5::internal
