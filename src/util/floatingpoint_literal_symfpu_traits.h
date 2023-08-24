/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain, Mathias Preiner
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
 *
 * !!! This header is only to be included in floating-point literal headers !!!
 *
 * This is a symfpu literal "back-end".  It allows the library to be used as
 * an arbitrary precision floating-point implementation.  This is effectively
 * the glue between symfpu's notion of "signed bit-vector" and cvc5's
 * BitVector.
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__FLOATINGPOINT_LITERAL_SYMFPU_TRAITS_H
#define CVC5__UTIL__FLOATINGPOINT_LITERAL_SYMFPU_TRAITS_H

#include <symfpu/core/unpackedFloat.h>

#include "util/bitvector.h"
#include "util/floatingpoint_size.h"
#include "util/roundingmode.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {
namespace symfpuLiteral {

/**
 * Forward declaration of wrapper so that traits can be defined early and so
 * used in the implementation of wrappedBitVector.
 */
template <bool T>
class wrappedBitVector;

using Cvc5BitWidth = uint32_t;
using Cvc5Prop = bool;
using Cvc5RM = cvc5::internal::RoundingMode;
using Cvc5FPSize = cvc5::internal::FloatingPointSize;
using Cvc5UnsignedBitVector = wrappedBitVector<false>;
using Cvc5SignedBitVector = wrappedBitVector<true>;

/**
 * This is the template parameter for symfpu's templates.
 */
class traits
{
 public:
  /** The six key types that symfpu uses. */
  using bwt = Cvc5BitWidth;           // bit-width type
  using prop = Cvc5Prop;              // boolean type
  using rm = Cvc5RM;                  // rounding-mode type
  using fpt = Cvc5FPSize;             // floating-point format type
  using ubv = Cvc5UnsignedBitVector;  // unsigned bit-vector type
  using sbv = Cvc5SignedBitVector;    // signed bit-vector type

  /** Give concrete instances of each rounding mode, mainly for comparisons. */
  static rm RNE(void);
  static rm RNA(void);
  static rm RTP(void);
  static rm RTN(void);
  static rm RTZ(void);

  /** The sympfu properties. */
  static void precondition(const prop& p);
  static void postcondition(const prop& p);
  static void invariant(const prop& p);
};

/**
 * Type function for mapping between types.
 */
template <bool T>
struct signedToLiteralType;

template <>
struct signedToLiteralType<true>
{
  using literalType = int32_t;
};
template <>
struct signedToLiteralType<false>
{
  using literalType = uint32_t;
};

/**
 * This extends the interface for cvc5::internal::BitVector for compatibility with symFPU.
 * The template parameter distinguishes signed and unsigned bit-vectors, a
 * distinction symfpu uses.
 */
template <bool isSigned>
class wrappedBitVector : public BitVector
{
 protected:
  using literalType = typename signedToLiteralType<isSigned>::literalType;
  friend wrappedBitVector<!isSigned>;  // To allow conversion between types

  friend ::symfpu::ite<Cvc5Prop, wrappedBitVector<isSigned> >;  // For ITE

 public:
  /** Constructors. */
  wrappedBitVector(const Cvc5BitWidth w, const uint32_t v) : BitVector(w, v) {}
  wrappedBitVector(const Cvc5Prop& p) : BitVector(1, p ? 1U : 0U) {}
  wrappedBitVector(const wrappedBitVector<isSigned>& old) : BitVector(old) {}
  wrappedBitVector(const BitVector& old) : BitVector(old) {}

  /** Get the bit-width of this wrapped bit-vector. */
  Cvc5BitWidth getWidth(void) const { return getSize(); }

  /** Create a zero value of given bit-width 'w'. */
  static wrappedBitVector<isSigned> one(const Cvc5BitWidth& w);
  /** Create a one value of given bit-width 'w'. */
  static wrappedBitVector<isSigned> zero(const Cvc5BitWidth& w);
  /** Create a ones value (all bits 1) of given bit-width 'w'. */
  static wrappedBitVector<isSigned> allOnes(const Cvc5BitWidth& w);
  /** Create a maximum signed/unsigned value of given bit-width 'w'. */
  static wrappedBitVector<isSigned> maxValue(const Cvc5BitWidth& w);
  /** Create a minimum signed/unsigned value of given bit-width 'w'. */
  static wrappedBitVector<isSigned> minValue(const Cvc5BitWidth& w);

  /** Return true if this a bit-vector representing a ones value. */
  Cvc5Prop isAllOnes() const;
  /** Return true if this a bit-vector representing a zero value. */
  Cvc5Prop isAllZeros() const;

  /** Left shift. */
  wrappedBitVector<isSigned> operator<<(
      const wrappedBitVector<isSigned>& op) const;
  /** Logical (unsigned) and arithmetic (signed) right shift. */
  wrappedBitVector<isSigned> operator>>(
      const wrappedBitVector<isSigned>& op) const;

  /**
   * Inherited but ...
   * *sigh* if we use the inherited version then it will return a
   * cvc5::internal::BitVector which can be converted back to a
   * wrappedBitVector<isSigned> but isn't done automatically when working
   * out types for templates instantiation.  ITE is a particular
   * problem as expressions and constants no longer derive the
   * same type.  There aren't any good solutions in C++, we could
   * use CRTP but Liana wouldn't appreciate that, so the following
   * pointless wrapping functions are needed.
   */

  /** Bit-wise or. */
  wrappedBitVector<isSigned> operator|(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-wise and. */
  wrappedBitVector<isSigned> operator&(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector addition. */
  wrappedBitVector<isSigned> operator+(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector subtraction. */
  wrappedBitVector<isSigned> operator-(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector multiplication. */
  wrappedBitVector<isSigned> operator*(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector signed/unsigned division. */
  wrappedBitVector<isSigned> operator/(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector signed/unsigned remainder. */
  wrappedBitVector<isSigned> operator%(
      const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector negation. */
  wrappedBitVector<isSigned> operator-(void) const;
  /** Bit-wise not. */
  wrappedBitVector<isSigned> operator~(void) const;

  /** Bit-vector increment. */
  wrappedBitVector<isSigned> increment() const;
  /** Bit-vector decrement. */
  wrappedBitVector<isSigned> decrement() const;
  /**
   * Bit-vector logical/arithmetic right shift where 'op' extended to the
   * bit-width of this wrapped bit-vector.
   */
  wrappedBitVector<isSigned> signExtendRightShift(
      const wrappedBitVector<isSigned>& op) const;

  /**
   * Modular operations.
   * Note: No overflow checking so these are the same as other operations.
   */
  wrappedBitVector<isSigned> modularLeftShift(
      const wrappedBitVector<isSigned>& op) const;
  wrappedBitVector<isSigned> modularRightShift(
      const wrappedBitVector<isSigned>& op) const;
  wrappedBitVector<isSigned> modularIncrement() const;
  wrappedBitVector<isSigned> modularDecrement() const;
  wrappedBitVector<isSigned> modularAdd(
      const wrappedBitVector<isSigned>& op) const;
  wrappedBitVector<isSigned> modularNegate() const;

  /** Bit-vector equality. */
  Cvc5Prop operator==(const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector signed/unsigned less or equal than. */
  Cvc5Prop operator<=(const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector sign/unsigned greater or equal than. */
  Cvc5Prop operator>=(const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector signed/unsigned less than. */
  Cvc5Prop operator<(const wrappedBitVector<isSigned>& op) const;
  /** Bit-vector sign/unsigned greater or equal than. */
  Cvc5Prop operator>(const wrappedBitVector<isSigned>& op) const;

  /** Convert this bit-vector to a signed bit-vector. */
  wrappedBitVector<true> toSigned(void) const;
  /** Convert this bit-vector to an unsigned bit-vector. */
  wrappedBitVector<false> toUnsigned(void) const;

  /** Bit-vector signed/unsigned (zero) extension. */
  wrappedBitVector<isSigned> extend(Cvc5BitWidth extension) const;

  /**
   * Create a "contracted" bit-vector by cutting off the 'reduction' number of
   * most significant bits, i.e., by extracting the (bit-width - reduction)
   * least significant bits.
   */
  wrappedBitVector<isSigned> contract(Cvc5BitWidth reduction) const;

  /**
   * Create a "resized" bit-vector of given size bei either extending (if new
   * size is larger) or contracting (if it is smaller) this wrapped bit-vector.
   */
  wrappedBitVector<isSigned> resize(Cvc5BitWidth newSize) const;

  /**
   * Create an extension of this bit-vector that matches the bit-width of the
   * given bit-vector.
   *
   * Note: The size of the given bit-vector may not be larger than the size of
   *       this bit-vector.
   */
  wrappedBitVector<isSigned> matchWidth(
      const wrappedBitVector<isSigned>& op) const;

  /** Bit-vector concatenation. */
  wrappedBitVector<isSigned> append(const wrappedBitVector<isSigned>& op) const;

  /** Inclusive of end points, thus if the same, extracts just one bit. */
  wrappedBitVector<isSigned> extract(Cvc5BitWidth upper,
                                     Cvc5BitWidth lower) const;
};
}  // namespace symfpuLiteral
}  // namespace cvc5::internal

#endif
