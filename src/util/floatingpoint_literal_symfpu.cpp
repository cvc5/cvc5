/*********************                                                        */
/*! \file floatingpoint_literal_symfpu.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SymFPU glue code for floating-point values.
 **/
#include "util/floatingpoint_literal_symfpu.h"

#include "base/check.h"

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
}  // namespace symfpu
#endif

/* -------------------------------------------------------------------------- */

namespace CVC4 {

uint32_t FloatingPointLiteral::getUnpackedExponentWidth(FloatingPointSize& size)
{
#ifdef CVC4_USE_SYMFPU
  return SymFPUUnpackedFloatLiteral::exponentWidth(size);
#else
  unimplemented();
  return 2;
#endif
}

uint32_t FloatingPointLiteral::getUnpackedSignificandWidth(
    FloatingPointSize& size)
{
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
      ,
      d_symuf(symfpu::unpack<symfpuLiteral::traits>(
          symfpuLiteral::CVC4FPSize(exp_size, sig_size), bv))
#endif
{
}

FloatingPointLiteral::FloatingPointLiteral(
    const FloatingPointSize& size, FloatingPointLiteral::SpecialConstKind kind)
    : d_fp_size(size)
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
      ,
      d_symuf(signedBV ? symfpu::convertSBVToFloat<symfpuLiteral::traits>(
                  symfpuLiteral::CVC4FPSize(size),
                  symfpuLiteral::CVC4RM(rm),
                  symfpuLiteral::CVC4SignedBitVector(bv))
                       : symfpu::convertUBVToFloat<symfpuLiteral::traits>(
                           symfpuLiteral::CVC4FPSize(size),
                           symfpuLiteral::CVC4RM(rm),
                           symfpuLiteral::CVC4UnsignedBitVector(bv)))
#endif
{
}

BitVector FloatingPointLiteral::pack(void) const
{
#ifdef CVC4_USE_SYMFPU
  BitVector bv(symfpu::pack<symfpuLiteral::traits>(d_fp_size, d_symuf));
#else
  unimplemented();
  BitVector bv(4u, 0u);
#endif
  return bv;
}

FloatingPointLiteral FloatingPointLiteral::absolute(void) const
{
#ifdef CVC4_USE_SYMFPU
  return FloatingPointLiteral(
      d_fp_size, symfpu::absolute<symfpuLiteral::traits>(d_fp_size, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::negate(void) const
{
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
  return FloatingPointLiteral(
      d_fp_size, symfpu::sqrt<symfpuLiteral::traits>(d_fp_size, rm, d_symuf));
#else
  unimplemented();
  return *this;
#endif
}

FloatingPointLiteral FloatingPointLiteral::rti(const RoundingMode& rm) const
{
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
  return d_symuf.exponent;
#else
  unimplemented();
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return BitVector();
#endif
}

BitVector FloatingPointLiteral::getSignificand() const
{
#ifdef CVC4_USE_SYMFPU
  return d_symuf.significand;
#else
  unimplemented();
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return BitVector();
#endif
}

bool FloatingPointLiteral::getSign() const
{
#ifdef CVC4_USE_SYMFPU
  return d_symuf.sign;
#else
  unimplemented();
  Unreachable() << "no concrete implementation of FloatingPointLiteral";
  return false;
#endif
}

bool FloatingPointLiteral::isNormal(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isNormal<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isSubnormal(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isSubnormal<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isZero(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isZero<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isInfinite(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isInfinite<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isNaN(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isNaN<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isNegative(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isNegative<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

bool FloatingPointLiteral::isPositive(void) const
{
#ifdef CVC4_USE_SYMFPU
  return symfpu::isPositive<symfpuLiteral::traits>(d_fp_size, d_symuf);
#else
  unimplemented();
  return false;
#endif
}

FloatingPointLiteral FloatingPointLiteral::convert(
    const FloatingPointSize& target, const RoundingMode& rm) const
{
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
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
#ifdef CVC4_USE_SYMFPU
  return symfpu::convertFloatToUBV<symfpuLiteral::traits>(
      d_fp_size, rm, d_symuf, width, undefinedCase);
#else
  unimplemented();
  return undefinedCase;
#endif
}

#ifndef CVC4_USE_SYMFPU
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

namespace symfpuLiteral {

// To simplify the property macros
typedef traits t;

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::one(
    const CVC4BitWidth& w)
{
  return wrappedBitVector<isSigned>(w, 1);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::zero(
    const CVC4BitWidth& w)
{
  return wrappedBitVector<isSigned>(w, 0);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::allOnes(
    const CVC4BitWidth& w)
{
  return ~wrappedBitVector<isSigned>::zero(w);
}

template <bool isSigned>
CVC4Prop wrappedBitVector<isSigned>::isAllOnes() const
{
  return (*this == wrappedBitVector<isSigned>::allOnes(getWidth()));
}
template <bool isSigned>
CVC4Prop wrappedBitVector<isSigned>::isAllZeros() const
{
  return (*this == wrappedBitVector<isSigned>::zero(getWidth()));
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::maxValue(
    const CVC4BitWidth& w)
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
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::minValue(
    const CVC4BitWidth& w)
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
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::leftShift(op);
}

template <>
wrappedBitVector<true> wrappedBitVector<true>::operator>>(
    const wrappedBitVector<true>& op) const
{
  return BitVector::arithRightShift(op);
}

template <>
wrappedBitVector<false> wrappedBitVector<false>::operator>>(
    const wrappedBitVector<false>& op) const
{
  return BitVector::logicalRightShift(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator|(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::operator|(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator&(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::operator&(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator+(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::operator+(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator-(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::operator-(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator*(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::operator*(op);
}

template <>
wrappedBitVector<false> wrappedBitVector<false>::operator/(
    const wrappedBitVector<false>& op) const
{
  return BitVector::unsignedDivTotal(op);
}

template <>
wrappedBitVector<false> wrappedBitVector<false>::operator%(
    const wrappedBitVector<false>& op) const
{
  return BitVector::unsignedRemTotal(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator-(void) const
{
  return BitVector::operator-();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator~(void) const
{
  return BitVector::operator~();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::increment() const
{
  return *this + wrappedBitVector<isSigned>::one(getWidth());
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::decrement() const
{
  return *this - wrappedBitVector<isSigned>::one(getWidth());
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::signExtendRightShift(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::arithRightShift(BitVector(getWidth(), op));
}

/*** Modular opertaions ***/
// No overflow checking so these are the same as other operations
template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularLeftShift(
    const wrappedBitVector<isSigned>& op) const
{
  return *this << op;
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularRightShift(
    const wrappedBitVector<isSigned>& op) const
{
  return *this >> op;
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularIncrement() const
{
  return increment();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularDecrement() const
{
  return decrement();
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::modularAdd(
    const wrappedBitVector<isSigned>& op) const
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
CVC4Prop wrappedBitVector<isSigned>::operator==(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::operator==(op);
}

template <>
CVC4Prop wrappedBitVector<true>::operator<=(
    const wrappedBitVector<true>& op) const
{
  return signedLessThanEq(op);
}

template <>
CVC4Prop wrappedBitVector<true>::operator>=(
    const wrappedBitVector<true>& op) const
{
  return !(signedLessThan(op));
}

template <>
CVC4Prop wrappedBitVector<true>::operator<(
    const wrappedBitVector<true>& op) const
{
  return signedLessThan(op);
}

template <>
CVC4Prop wrappedBitVector<true>::operator>(
    const wrappedBitVector<true>& op) const
{
  return !(signedLessThanEq(op));
}

template <>
CVC4Prop wrappedBitVector<false>::operator<=(
    const wrappedBitVector<false>& op) const
{
  return unsignedLessThanEq(op);
}

template <>
CVC4Prop wrappedBitVector<false>::operator>=(
    const wrappedBitVector<false>& op) const
{
  return !(unsignedLessThan(op));
}

template <>
CVC4Prop wrappedBitVector<false>::operator<(
    const wrappedBitVector<false>& op) const
{
  return unsignedLessThan(op);
}

template <>
CVC4Prop wrappedBitVector<false>::operator>(
    const wrappedBitVector<false>& op) const
{
  return !(unsignedLessThanEq(op));
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
    CVC4BitWidth extension) const
{
  if (isSigned)
  {
    return BitVector::signExtend(extension);
  }
  else
  {
    return BitVector::zeroExtend(extension);
  }
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::contract(
    CVC4BitWidth reduction) const
{
  Assert(getWidth() > reduction);

  return extract((getWidth() - 1) - reduction, 0);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::resize(
    CVC4BitWidth newSize) const
{
  CVC4BitWidth width = getWidth();

  if (newSize > width)
  {
    return extend(newSize - width);
  }
  else if (newSize < width)
  {
    return contract(width - newSize);
  }
  else
  {
    return *this;
  }
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::matchWidth(
    const wrappedBitVector<isSigned>& op) const
{
  Assert(getWidth() <= op.getWidth());
  return extend(op.getWidth() - getWidth());
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::append(
    const wrappedBitVector<isSigned>& op) const
{
  return BitVector::concat(op);
}

// Inclusive of end points, thus if the same, extracts just one bit
template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::extract(
    CVC4BitWidth upper, CVC4BitWidth lower) const
{
  Assert(upper >= lower);
  return BitVector::extract(upper, lower);
}

// Explicit instantiation
template class wrappedBitVector<true>;
template class wrappedBitVector<false>;

traits::rm traits::RNE(void) { return ::CVC4::ROUND_NEAREST_TIES_TO_EVEN; };
traits::rm traits::RNA(void) { return ::CVC4::ROUND_NEAREST_TIES_TO_AWAY; };
traits::rm traits::RTP(void) { return ::CVC4::ROUND_TOWARD_POSITIVE; };
traits::rm traits::RTN(void) { return ::CVC4::ROUND_TOWARD_NEGATIVE; };
traits::rm traits::RTZ(void) { return ::CVC4::ROUND_TOWARD_ZERO; };
// This is a literal back-end so props are actually bools
// so these can be handled in the same way as the internal assertions above

void traits::precondition(const traits::prop& p)
{
  Assert(p);
  return;
}
void traits::postcondition(const traits::prop& p)
{
  Assert(p);
  return;
}
void traits::invariant(const traits::prop& p)
{
  Assert(p);
  return;
}
}  // namespace symfpuLiteral

}  // namespace CVC4
