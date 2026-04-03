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
 *
 * !!! This header is not to be included in any other headers !!!
 */
#include "cvc5_public.h"

#ifndef CVC5__UTIL__FLOATINGPOINT_LITERAL_SYMFPU_H
#define CVC5__UTIL__FLOATINGPOINT_LITERAL_SYMFPU_H

#include "util/bitvector.h"
#include "util/floatingpoint_literal.h"
#include "util/floatingpoint_literal_symfpu_traits.h"
#include "util/floatingpoint_size.h"
#include "util/roundingmode.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

using SymFPUUnpackedFloatLiteral =
    ::symfpu::unpackedFloat<symfpuLiteral::traits>;

class FloatingPointLiteralSymFPU : public FloatingPointLiteral
{
  friend class FloatingPoint;

 public:
  /** Create a FP literal from its IEEE bit-vector representation. */
  FloatingPointLiteralSymFPU(uint32_t exp_size,
                             uint32_t sig_size,
                             const BitVector& bv);
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             const BitVector& bv);

  /** Create a FP literal that represents a special constants. */
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             SpecialConstKind kind);
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             SpecialConstKind kind,
                             bool sign);

  /**
   * Create a FP literal from a signed or unsigned bit-vector value with
   * respect to given rounding mode.
   */
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             const RoundingMode& rm,
                             const BitVector& bv,
                             bool signedBV);

  /** Destructor. */
  ~FloatingPointLiteralSymFPU();

  /**
   * Create a FP literal from unpacked representation.
   */
  static std::unique_ptr<FloatingPointLiteral> fromUnpacked(
      const FloatingPointSize& size,
      bool sign,
      const BitVector& exp,
      const BitVector& sig);

  /**
   * Create a FP literal from a rational value with respect to given rounding
   * mode.
   */
  static std::unique_ptr<FloatingPointLiteral> fromRational(
      const FloatingPointSize& size, const RoundingMode& rm, const Rational& r);

  /* ---------------------------------------------------------------------- */
  /* FloatingPointLiteral interface                                         */
  /* ---------------------------------------------------------------------- */

  std::unique_ptr<FloatingPointLiteral> clone() const override;

  BitVector pack() const override;

  std::unique_ptr<FloatingPointLiteral> absolute() const override;
  std::unique_ptr<FloatingPointLiteral> negate() const override;
  std::unique_ptr<FloatingPointLiteral> add(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const override;
  std::unique_ptr<FloatingPointLiteral> sub(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const override;
  std::unique_ptr<FloatingPointLiteral> mult(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const override;
  std::unique_ptr<FloatingPointLiteral> div(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const override;
  std::unique_ptr<FloatingPointLiteral> fma(
      const RoundingMode& rm,
      const FloatingPointLiteral& arg1,
      const FloatingPointLiteral& arg2) const override;
  std::unique_ptr<FloatingPointLiteral> sqrt(
      const RoundingMode& rm) const override;
  std::unique_ptr<FloatingPointLiteral> rti(
      const RoundingMode& rm) const override;
  std::unique_ptr<FloatingPointLiteral> rem(
      const FloatingPointLiteral& arg) const override;

  std::unique_ptr<FloatingPointLiteral> maxTotal(
      const FloatingPointLiteral& arg, bool zeroCaseLeft) const override;
  std::unique_ptr<FloatingPointLiteral> minTotal(
      const FloatingPointLiteral& arg, bool zeroCaseLeft) const override;

  bool operator==(const FloatingPointLiteral& fp) const override;
  bool operator<=(const FloatingPointLiteral& arg) const override;
  bool operator<(const FloatingPointLiteral& arg) const override;

  BitVector getExponent() const override;
  BitVector getSignificand() const override;
  bool getSign() const override;

  bool isNormal() const override;
  bool isSubnormal() const override;
  bool isZero() const override;
  bool isInfinite() const override;
  bool isNaN() const override;
  bool isNegative() const override;
  bool isPositive() const override;

  std::unique_ptr<FloatingPointLiteral> convert(
      const FloatingPointSize& target, const RoundingMode& rm) const override;

  BitVector convertToSBVTotal(BitVectorSize width,
                              const RoundingMode& rm,
                              BitVector undefinedCase) const override;
  BitVector convertToUBVTotal(BitVectorSize width,
                              const RoundingMode& rm,
                              BitVector undefinedCase) const override;

 private:
  /**
   * Create a FP literal from unpacked representation.
   *
   * This unpacked representation accounts for additional bits required for the
   * exponent to allow subnormals to be normalized.
   *
   * This should NOT be used to create a literal from its IEEE bit-vector
   * representation -- for this, the above constructor is to be used while
   * creating a SymFPUUnpackedFloatLiteral via symfpu::unpack.
   */
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             const bool sign,
                             const BitVector& exp,
                             const BitVector& sig)
      : FloatingPointLiteral(size),
        d_symuf(SymFPUUnpackedFloatLiteral(sign, exp, sig))
  {
  }

  /** Create a FP literal from a symFPU unpacked float. */
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             SymFPUUnpackedFloatLiteral symuf)
      : FloatingPointLiteral(size), d_symuf(symuf)
  {
  }

  /** The actual floating-point value, a SymFPU unpackedFloat. */
  SymFPUUnpackedFloatLiteral d_symuf;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc5::internal

#endif
