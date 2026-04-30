/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * MPFR-based floating-point literal implementation.
 *
 * !!! This header is not to be included in any other headers !!!
 */
#ifndef CVC5__UTIL__FLOATINGPOINT_LITERAL_MPFR_H
#define CVC5__UTIL__FLOATINGPOINT_LITERAL_MPFR_H

#include "cvc5_public.h"

// Enable C99 variadic macro version of mpfr_round_nearest_away so that
// multi-argument operations (add, mul, fma, ...) work correctly in C++.
#ifndef MPFR_USE_C99_FEATURE
#define MPFR_USE_C99_FEATURE 1
#endif
#include <mpfr.h>

#include "util/bitvector.h"
#include "util/floatingpoint_literal.h"
#include "util/floatingpoint_size.h"
#include "util/roundingmode.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

class FloatingPointLiteralMPFR : public FloatingPointLiteral
{
 public:
  /** Constructors. */

  /** Create a FP literal from its IEEE bit-vector representation. */
  FloatingPointLiteralMPFR(uint32_t exp_size,
                           uint32_t sig_size,
                           const BitVector& bv);
  FloatingPointLiteralMPFR(const FloatingPointSize& size, const BitVector& bv);

  /** Create a FP literal that represents a special constant. */
  FloatingPointLiteralMPFR(const FloatingPointSize& size,
                           SpecialConstKind kind);
  FloatingPointLiteralMPFR(const FloatingPointSize& size,
                           SpecialConstKind kind,
                           bool sign);

  /**
   * Create a FP literal from a signed or unsigned bit-vector value with
   * respect to given rounding mode.
   */
  FloatingPointLiteralMPFR(const FloatingPointSize& size,
                           const RoundingMode& rm,
                           const BitVector& bv,
                           bool signedBV);

  /** Copy constructor. */
  FloatingPointLiteralMPFR(const FloatingPointLiteralMPFR& other);
  /** Move constructor. */
  FloatingPointLiteralMPFR(FloatingPointLiteralMPFR&& other);

  /** Copy assignment. */
  FloatingPointLiteralMPFR& operator=(const FloatingPointLiteralMPFR& other);
  /** Move assignment. */
  FloatingPointLiteralMPFR& operator=(FloatingPointLiteralMPFR&& other);

  ~FloatingPointLiteralMPFR() override;

  /**
   * Create a FP literal from a rational value with respect to given rounding
   * mode.  MPFR-specific implementation.
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

  BitVector getUnpackedExponent() const override;
  BitVector getUnpackedSignificand() const override;
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
  std::pair<Rational, bool> convertToRational() const override;

 private:
  /**
   * Convert cvc5 RoundingMode to MPFR rounding mode.
   */
  static mpfr_rnd_t rmToMpfr(const RoundingMode& rm);

  /**
   * Initialize the MPFR variable for the given format.
   * Called by constructors.
   */
  void initMpfr();

  /**
   * Set MPFR emin/emax globals for this literal's format.
   */
  void setMpfrFormat() const;

  /** The underlying MPFR representation. */
  mpfr_t d_mpfr;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc5::internal

#endif
