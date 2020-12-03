/*********************                                                        */
/*! \file floatingpoint_literal_symfpu.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SymFPU glue code for floating-point values.
 **/
#include "util/floatingpoint_literal_symfpu.h"

#include "base/check.h"

namespace CVC4 {

#ifndef CVC4_USE_SYMFPU
void FloatingPointLiteral::unfinished(void) const
{
  Unimplemented() << "Floating-point literals not yet implemented.";
}

bool FloatingPointLiteral::operator==(const FloatingPointLiteral& other) const
{
  unfinished();
  return false;
}

size_t FloatingPointLiteral::hash(void) const
{
  unfinished();
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
