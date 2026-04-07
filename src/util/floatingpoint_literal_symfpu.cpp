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
#include "symfpu/utils/numberOfRoundingModes.h"
#include "symfpu/utils/properties.h"

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

uint32_t FloatingPointLiteralSymFPU::getUnpackedExponentWidth(
    FloatingPointSize& size)
{
  return SymFPUUnpackedFloatLiteral::exponentWidth(size);
}

uint32_t FloatingPointLiteralSymFPU::getUnpackedSignificandWidth(
    FloatingPointSize& size)
{
  return SymFPUUnpackedFloatLiteral::significandWidth(size);
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(uint32_t exp_size,
                                                       uint32_t sig_size,
                                                       const BitVector& bv)
    : d_fp_size(exp_size, sig_size),
      d_symuf(symfpu::unpack<symfpuLiteral::traits>(
          symfpuLiteral::Cvc5FPSize(exp_size, sig_size), bv))
{
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size,
    CVC5_UNUSED FloatingPointLiteralSymFPU::SpecialConstKind kind)
    : d_fp_size(size), d_symuf(SymFPUUnpackedFloatLiteral::makeNaN(size))
{
  Assert(kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPNAN);
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size,
    FloatingPointLiteralSymFPU::SpecialConstKind kind,
    bool sign)
    : d_fp_size(size),
      d_symuf(kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPINF
                  ? SymFPUUnpackedFloatLiteral::makeInf(size, sign)
                  : SymFPUUnpackedFloatLiteral::makeZero(size, sign))
{
  Assert(kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPINF
         || kind == FloatingPointLiteralSymFPU::SpecialConstKind::FPZERO);
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size, const BitVector& bv)
    : d_fp_size(size), d_symuf(symfpu::unpack<symfpuLiteral::traits>(size, bv))
{
}

FloatingPointLiteralSymFPU::FloatingPointLiteralSymFPU(
    const FloatingPointSize& size,
    const RoundingMode& rm,
    const BitVector& bv,
    bool signedBV)
    : d_fp_size(size),
      d_symuf(signedBV ? symfpu::convertSBVToFloat<symfpuLiteral::traits>(
                             symfpuLiteral::Cvc5FPSize(size),
                             symfpuLiteral::Cvc5RM(rm),
                             symfpuLiteral::Cvc5SignedBitVector(bv))
                       : symfpu::convertUBVToFloat<symfpuLiteral::traits>(
                             symfpuLiteral::Cvc5FPSize(size),
                             symfpuLiteral::Cvc5RM(rm),
                             symfpuLiteral::Cvc5UnsignedBitVector(bv)))
{
}

BitVector FloatingPointLiteralSymFPU::pack(void) const
{
  BitVector bv(symfpu::pack<symfpuLiteral::traits>(d_fp_size, d_symuf));
  return bv;
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::absolute(void) const
{
  return FloatingPointLiteralSymFPU(
      d_fp_size, symfpu::absolute<symfpuLiteral::traits>(d_fp_size, d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::negate(void) const
{
  return FloatingPointLiteralSymFPU(
      d_fp_size, symfpu::negate<symfpuLiteral::traits>(d_fp_size, d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::add(
    const RoundingMode& rm, const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::add<symfpuLiteral::traits>(
          d_fp_size, rm, d_symuf, arg.d_symuf, true));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::sub(
    const RoundingMode& rm, const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::add<symfpuLiteral::traits>(
          d_fp_size, rm, d_symuf, arg.d_symuf, false));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::mult(
    const RoundingMode& rm, const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(d_fp_size,
                                    symfpu::multiply<symfpuLiteral::traits>(
                                        d_fp_size, rm, d_symuf, arg.d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::div(
    const RoundingMode& rm, const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(d_fp_size,
                                    symfpu::divide<symfpuLiteral::traits>(
                                        d_fp_size, rm, d_symuf, arg.d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::fma(
    const RoundingMode& rm,
    const FloatingPointLiteralSymFPU& arg1,
    const FloatingPointLiteralSymFPU& arg2) const
{
  Assert(d_fp_size == arg1.d_fp_size);
  Assert(d_fp_size == arg2.d_fp_size);
  return FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::fma<symfpuLiteral::traits>(
          d_fp_size, rm, d_symuf, arg1.d_symuf, arg2.d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::sqrt(
    const RoundingMode& rm) const
{
  return FloatingPointLiteralSymFPU(
      d_fp_size, symfpu::sqrt<symfpuLiteral::traits>(d_fp_size, rm, d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::rti(
    const RoundingMode& rm) const
{
  return FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::roundToIntegral<symfpuLiteral::traits>(d_fp_size, rm, d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::rem(
    const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(d_fp_size,
                                    symfpu::remainder<symfpuLiteral::traits>(
                                        d_fp_size, d_symuf, arg.d_symuf));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::maxTotal(
    const FloatingPointLiteralSymFPU& arg, bool zeroCaseLeft) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::max<symfpuLiteral::traits>(
          d_fp_size, d_symuf, arg.d_symuf, zeroCaseLeft));
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::minTotal(
    const FloatingPointLiteralSymFPU& arg, bool zeroCaseLeft) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteralSymFPU(
      d_fp_size,
      symfpu::min<symfpuLiteral::traits>(
          d_fp_size, d_symuf, arg.d_symuf, zeroCaseLeft));
}

bool FloatingPointLiteralSymFPU::operator==(
    const FloatingPointLiteralSymFPU& fp) const
{
  return ((d_fp_size == fp.d_fp_size)
          && symfpu::smtlibEqual<symfpuLiteral::traits>(
              d_fp_size, d_symuf, fp.d_symuf));
}

bool FloatingPointLiteralSymFPU::operator<=(
    const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return symfpu::lessThanOrEqual<symfpuLiteral::traits>(
      d_fp_size, d_symuf, arg.d_symuf);
}

bool FloatingPointLiteralSymFPU::operator<(
    const FloatingPointLiteralSymFPU& arg) const
{
  Assert(d_fp_size == arg.d_fp_size);
  return symfpu::lessThan<symfpuLiteral::traits>(
      d_fp_size, d_symuf, arg.d_symuf);
}

BitVector FloatingPointLiteralSymFPU::getExponent() const
{
  return d_symuf.exponent;
}

BitVector FloatingPointLiteralSymFPU::getSignificand() const
{
  return d_symuf.significand;
}

bool FloatingPointLiteralSymFPU::getSign() const { return d_symuf.sign; }

bool FloatingPointLiteralSymFPU::isNormal(void) const
{
  return symfpu::isNormal<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

bool FloatingPointLiteralSymFPU::isSubnormal(void) const
{
  return symfpu::isSubnormal<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

bool FloatingPointLiteralSymFPU::isZero(void) const
{
  return symfpu::isZero<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

bool FloatingPointLiteralSymFPU::isInfinite(void) const
{
  return symfpu::isInfinite<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

bool FloatingPointLiteralSymFPU::isNaN(void) const
{
  return symfpu::isNaN<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

bool FloatingPointLiteralSymFPU::isNegative(void) const
{
  return symfpu::isNegative<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

bool FloatingPointLiteralSymFPU::isPositive(void) const
{
  return symfpu::isPositive<symfpuLiteral::traits>(d_fp_size, d_symuf);
}

FloatingPointLiteralSymFPU FloatingPointLiteralSymFPU::convert(
    const FloatingPointSize& target, const RoundingMode& rm) const
{
  return FloatingPointLiteralSymFPU(
      target,
      symfpu::convertFloatToFloat<symfpuLiteral::traits>(
          d_fp_size, target, rm, d_symuf));
}

BitVector FloatingPointLiteralSymFPU::convertToSBVTotal(
    BitVectorSize width, const RoundingMode& rm, BitVector undefinedCase) const
{
  return symfpu::convertFloatToSBV<symfpuLiteral::traits>(
      d_fp_size, rm, d_symuf, width, undefinedCase);
}

BitVector FloatingPointLiteralSymFPU::convertToUBVTotal(
    BitVectorSize width, const RoundingMode& rm, BitVector undefinedCase) const
{
  return symfpu::convertFloatToUBV<symfpuLiteral::traits>(
      d_fp_size, rm, d_symuf, width, undefinedCase);
}

}  // namespace cvc5::internal
