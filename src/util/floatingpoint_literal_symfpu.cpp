/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SymFPU glue code for floating-point values.
 */
#include "util/floatingpoint_literal_symfpu.h"

#include "base/check.h"

#ifdef CVC5_USE_SYMFPU
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

#ifdef CVC5_USE_SYMFPU
namespace symfpu {

#define CVC5_LIT_ITE_DFN(T)                                            \
  template <>                                                          \
  struct ite<::cvc5::symfpuLiteral::Cvc5Prop, T>                       \
  {                                                                    \
    static const T& iteOp(const ::cvc5::symfpuLiteral::Cvc5Prop& cond, \
                          const T& l,                                  \
                          const T& r)                                  \
    {                                                                  \
      return cond ? l : r;                                             \
    }                                                                  \
  }

CVC5_LIT_ITE_DFN(::cvc5::symfpuLiteral::traits::rm);
CVC5_LIT_ITE_DFN(::cvc5::symfpuLiteral::traits::prop);
CVC5_LIT_ITE_DFN(::cvc5::symfpuLiteral::traits::sbv);
CVC5_LIT_ITE_DFN(::cvc5::symfpuLiteral::traits::ubv);

#undef CVC5_LIT_ITE_DFN
}  // namespace symfpu
#endif

/* -------------------------------------------------------------------------- */

namespace cvc5 {

uint32_t FloatingPointLiteral::getUnpackedExponentWidth(FloatingPointSize& size)
{
#ifdef CVC5_USE_SYMFPU
  return SymFPUUnpackedFloatLiteral::exponentWidth(size);
#else
  unimplemented();
  return 2;
#endif
}

uint32_t FloatingPointLiteral::getUnpackedSignificandWidth(
    FloatingPointSize& size)
{
#ifdef CVC5_USE_SYMFPU
  return SymFPUUnpackedFloatLiteral::significandWidth(size);
#else
  unimplemented();
  return 2;
#endif
}

FloatingPointLiteral::FloatingPointLiteral(uint32_t exp_size,
                                           uint32_t sig_size,
                                           const BitVector& bv)
    : d_fp_size(exp_size, sig_size)
#ifdef CVC5_USE_SYMFPU
      ,
      d_symuf(symfpu::unpack<symfpuLiteral::traits>(
          symfpuLiteral::Cvc5FPSize(exp_size, sig_size), bv))
#endif
{
}

FloatingPointLiteral::FloatingPointLiteral(
    const FloatingPointSize& size, FloatingPointLiteral::SpecialConstKind kind)
    : d_fp_size(size)
#ifdef CVC5_USE_SYMFPU
      ,
      d_symuf(SymFPUUnpackedFloatLiteral::makeNaN(size))
#endif
{
  Assert(kind == FloatingPointLiteral::SpecialConstKind::FPNAN);
}

FloatingPointLiteral::FloatingPointLiteral(
    const FloatingPointSize& size,
    FloatingPointLiteral::SpecialConstKind kind,
    bool sign)
    : d_fp_size(size)
#ifdef CVC5_USE_SYMFPU
      ,
      d_symuf(kind == FloatingPointLiteral::SpecialConstKind::FPINF
                  ? SymFPUUnpackedFloatLiteral::makeInf(size, sign)
                  : SymFPUUnpackedFloatLiteral::makeZero(size, sign))
#endif
{
  Assert(kind == FloatingPointLiteral::SpecialConstKind::FPINF
         || kind == FloatingPointLiteral::SpecialConstKind::FPZERO);
}

FloatingPointLiteral::FloatingPointLiteral(const FloatingPointSize& size,
                                           const BitVector& bv)
    : d_fp_size(size)
#ifdef CVC5_USE_SYMFPU
      ,
      d_symuf(symfpu::unpack<symfpuLiteral::traits>(size, bv))
#endif
{
}

FloatingPointLiteral::FloatingPointLiteral(const FloatingPointSize& size,
                                           const RoundingMode& rm,
                                           const BitVector& bv,
                                           bool signedBV)
    : d_fp_size(size)
#ifdef CVC5_USE_SYMFPU
      ,
      d_symuf(signedBV ? symfpu::convertSBVToFloat<symfpuLiteral::traits>(
                  symfpuLiteral::Cvc5FPSize(size),
                  symfpuLiteral::Cvc5RM(rm),
                  symfpuLiteral::Cvc5SignedBitVector(bv))
                       : symfpu::convertUBVToFloat<symfpuLiteral::traits>(
                           symfpuLiteral::Cvc5FPSize(size),
                           symfpuLiteral::Cvc5RM(rm),
                           symfpuLiteral::Cvc5UnsignedBitVector(bv)))
#endif
{
}

BitVector FloatingPointLiteral::pack(void) const
{
#ifdef CVC5_USE_SYMFPU
  BitVector bv(symfpu::pack<symfpuLiteral::traits>(d_fp_size, d_symuf));
#else
  unimplemented();
  BitVector bv(4u, 0u);
#endif
  return bv;
}

FloatingPointLiteral FloatingPointLiteral::absolute(void) const
{
#ifdef CVC5_USE_SYMFPU
  return FloatingPointLiteral(
      d_fp_size, symfpu::absolute<symfpuLiteral::traits>(d_fp_size, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::negate(void) const
{
#ifdef CVC5_USE_SYMFPU
  return FloatingPointLiteral(
      d_fp_size, symfpu::negate<symfpuLiteral::traits>(d_fp_size, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::add(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(d_fp_size,
                              symfpu::add<symfpuLiteral::traits>(
                                  d_fp_size, rm, d_symuf, arg.d_symuf, true));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::sub(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(d_fp_size,
                              symfpu::add<symfpuLiteral::traits>(
                                  d_fp_size, rm, d_symuf, arg.d_symuf, false));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::mult(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(d_fp_size,
                              symfpu::multiply<symfpuLiteral::traits>(
                                  d_fp_size, rm, d_symuf, arg.d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::div(
    const RoundingMode& rm, const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(d_fp_size,
                              symfpu::divide<symfpuLiteral::traits>(
                                  d_fp_size, rm, d_symuf, arg.d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::fma(
    const RoundingMode& rm,
    const FloatingPointLiteral& arg1,
    const FloatingPointLiteral& arg2) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg1.d_fp_size);
  Assert(d_fp_size == arg2.d_fp_size);
  return FloatingPointLiteral(
      d_fp_size,
      symfpu::fma<symfpuLiteral::traits>(
          d_fp_size, rm, d_symuf, arg1.d_symuf, arg2.d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::sqrt(const RoundingMode& rm) const
{
#ifdef CVC5_USE_SYMFPU
  return FloatingPointLiteral(
      d_fp_size, symfpu::sqrt<symfpuLiteral::traits>(d_fp_size, rm, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::rti(const RoundingMode& rm) const
{
#ifdef CVC5_USE_SYMFPU
  return FloatingPointLiteral(
      d_fp_size,
      symfpu::roundToIntegral<symfpuLiteral::traits>(d_fp_size, rm, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::rem(
    const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(d_fp_size,
                              symfpu::remainder<symfpuLiteral::traits>(
                                  d_fp_size, d_symuf, arg.d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::maxTotal(
    const FloatingPointLiteral& arg, bool zeroCaseLeft) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(
      d_fp_size,
      symfpu::max<symfpuLiteral::traits>(
          d_fp_size, d_symuf, arg.d_symuf, zeroCaseLeft));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::minTotal(
    const FloatingPointLiteral& arg, bool zeroCaseLeft) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return FloatingPointLiteral(
      d_fp_size,
      symfpu::min<symfpuLiteral::traits>(
          d_fp_size, d_symuf, arg.d_symuf, zeroCaseLeft));
#else
  unimplemented();
  return *this;
#endif
}

bool FloatingPointLiteral::operator==(const FloatingPointLiteral& fp) const
{
#ifdef CVC5_USE_SYMFPU
  return ((d_fp_size == fp.d_fp_size)
          && symfpu::smtlibEqual<symfpuLiteral::traits>(
              d_fp_size, d_symuf, fp.d_symuf));
#else
  unimplemented();
  return ((d_fp_size == fp.d_fp_size));
#endif
}

bool FloatingPointLiteral::operator<=(const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return symfpu::lessThanOrEqual<symfpuLiteral::traits>(
      d_fp_size, d_symuf, arg.d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::operator<(const FloatingPointLiteral& arg) const
{
#ifdef CVC5_USE_SYMFPU
  Assert(d_fp_size == arg.d_fp_size);
  return symfpu::lessThan<symfpuLiteral::traits>(
      d_fp_size, d_symuf, arg.d_symuf);
#else
  unimplemented();
  return false;
#endif
}

BitVector FloatingPointLiteral::getExponent() const
{
#ifdef CVC5_USE_SYMFPU
  return d_symuf.exponent;
#else
  unimplemented();
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return BitVector();
#endif
}

BitVector FloatingPointLiteral::getSignificand() const
{
#ifdef CVC5_USE_SYMFPU
  return d_symuf.significand;
#else
  unimplemented();
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return BitVector();
#endif
}

bool FloatingPointLiteral::getSign() const
{
#ifdef CVC5_USE_SYMFPU
  return d_symuf.sign;
#else
  unimplemented();
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return false;
#endif
}

bool FloatingPointLiteral::isNormal(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isNormal<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isSubnormal(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isSubnormal<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isZero(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isZero<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isInfinite(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isInfinite<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isNaN(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isNaN<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isNegative(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isNegative<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isPositive(void) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::isPositive<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

FloatingPointLiteral FloatingPointLiteral::convert(
    const FloatingPointSize& target, const RoundingMode& rm) const
{
#ifdef CVC5_USE_SYMFPU
  return FloatingPointLiteral(
      target,
      symfpu::convertFloatToFloat<symfpuLiteral::traits>(
          d_fp_size, target, rm, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

BitVector FloatingPointLiteral::convertToSBVTotal(BitVectorSize width,
                                                  const RoundingMode& rm,
                                                  BitVector undefinedCase) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::convertFloatToSBV<symfpuLiteral::traits>(
      d_fp_size, rm, d_symuf, width, undefinedCase);
#else
  unimplemented();
  return undefinedCase;
#endif
}

BitVector FloatingPointLiteral::convertToUBVTotal(BitVectorSize width,
                                                  const RoundingMode& rm,
                                                  BitVector undefinedCase) const
{
#ifdef CVC5_USE_SYMFPU
  return symfpu::convertFloatToUBV<symfpuLiteral::traits>(
      d_fp_size, rm, d_symuf, width, undefinedCase);
#else
  unimplemented();
  return undefinedCase;
#endif
}

#ifndef CVC5_USE_SYMFPU
void FloatingPointLiteral::unimplemented(void)
{
  Unimplemented() << "no concrete implementation of FloatingPointLiteral";
}

size_t FloatingPointLiteral::hash(void) const
{
  unimplemented();
  return 23;
}
#endif

}  // namespace cvc5
