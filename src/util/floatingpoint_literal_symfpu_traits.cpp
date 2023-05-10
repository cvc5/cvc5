/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SymFPU glue code for floating-point values.
 */

#include "util/floatingpoint_literal_symfpu_traits.h"

#include "base/check.h"

namespace cvc5::internal {
namespace symfpuLiteral {

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::one(
    const Cvc5BitWidth& w)
{
  return wrappedBitVector<isSigned>(w, 1);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::zero(
    const Cvc5BitWidth& w)
{
  return wrappedBitVector<isSigned>(w, 0);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::allOnes(
    const Cvc5BitWidth& w)
{
  return ~wrappedBitVector<isSigned>::zero(w);
}

template <bool isSigned>
Cvc5Prop wrappedBitVector<isSigned>::isAllOnes() const
{
  return (*this == wrappedBitVector<isSigned>::allOnes(getWidth()));
}
template <bool isSigned>
Cvc5Prop wrappedBitVector<isSigned>::isAllZeros() const
{
  return (*this == wrappedBitVector<isSigned>::zero(getWidth()));
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::maxValue(
    const Cvc5BitWidth& w)
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
    const Cvc5BitWidth& w)
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
  return static_cast<const BitVector&>(*this)
         | static_cast<const BitVector&>(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator&(
    const wrappedBitVector<isSigned>& op) const
{
  return static_cast<const BitVector&>(*this)
         & static_cast<const BitVector&>(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator+(
    const wrappedBitVector<isSigned>& op) const
{
  return static_cast<const BitVector&>(*this)
         + static_cast<const BitVector&>(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator-(
    const wrappedBitVector<isSigned>& op) const
{
  return static_cast<const BitVector&>(*this)
         - static_cast<const BitVector&>(op);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator*(
    const wrappedBitVector<isSigned>& op) const
{
  return static_cast<const BitVector&>(*this)
         * static_cast<const BitVector&>(op);
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
  return -(static_cast<const BitVector&>(*this));
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::operator~(void) const
{
  return ~(static_cast<const BitVector&>(*this));
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
Cvc5Prop wrappedBitVector<isSigned>::operator==(
    const wrappedBitVector<isSigned>& op) const
{
  return static_cast<const BitVector&>(*this)
         == static_cast<const BitVector&>(op);
}

template <>
Cvc5Prop wrappedBitVector<true>::operator<=(
    const wrappedBitVector<true>& op) const
{
  return signedLessThanEq(op);
}

template <>
Cvc5Prop wrappedBitVector<true>::operator>=(
    const wrappedBitVector<true>& op) const
{
  return !(signedLessThan(op));
}

template <>
Cvc5Prop wrappedBitVector<true>::operator<(
    const wrappedBitVector<true>& op) const
{
  return signedLessThan(op);
}

template <>
Cvc5Prop wrappedBitVector<true>::operator>(
    const wrappedBitVector<true>& op) const
{
  return !(signedLessThanEq(op));
}

template <>
Cvc5Prop wrappedBitVector<false>::operator<=(
    const wrappedBitVector<false>& op) const
{
  return unsignedLessThanEq(op);
}

template <>
Cvc5Prop wrappedBitVector<false>::operator>=(
    const wrappedBitVector<false>& op) const
{
  return !(unsignedLessThan(op));
}

template <>
Cvc5Prop wrappedBitVector<false>::operator<(
    const wrappedBitVector<false>& op) const
{
  return unsignedLessThan(op);
}

template <>
Cvc5Prop wrappedBitVector<false>::operator>(
    const wrappedBitVector<false>& op) const
{
  return !(unsignedLessThanEq(op));
}

/*** Type conversion ***/

// Node makes no distinction between signed and unsigned, thus ...
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
    Cvc5BitWidth extension) const
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
    Cvc5BitWidth reduction) const
{
  Assert(getWidth() > reduction);

  return extract((getWidth() - 1) - reduction, 0);
}

template <bool isSigned>
wrappedBitVector<isSigned> wrappedBitVector<isSigned>::resize(
    Cvc5BitWidth newSize) const
{
  Cvc5BitWidth width = getWidth();

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
    Cvc5BitWidth upper, Cvc5BitWidth lower) const
{
  Assert(upper >= lower);
  return BitVector::extract(upper, lower);
}

// Explicit instantiation
template class wrappedBitVector<true>;
template class wrappedBitVector<false>;

traits::rm traits::RNE(void)
{
  return RoundingMode::ROUND_NEAREST_TIES_TO_EVEN;
};
traits::rm traits::RNA(void)
{
  return RoundingMode::ROUND_NEAREST_TIES_TO_AWAY;
};
traits::rm traits::RTP(void) { return RoundingMode::ROUND_TOWARD_POSITIVE; };
traits::rm traits::RTN(void) { return RoundingMode::ROUND_TOWARD_NEGATIVE; };
traits::rm traits::RTZ(void) { return RoundingMode::ROUND_TOWARD_ZERO; };
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
}  // namespace cvc5::internal
