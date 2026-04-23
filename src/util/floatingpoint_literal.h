/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base class for floating-point literal implementations.
 */

#ifndef CVC5__UTIL__FLOATINGPOINT_LITERAL_H
#define CVC5__UTIL__FLOATINGPOINT_LITERAL_H

#include <memory>
#include <utility>

#include "util/bitvector.h"
#include "util/floatingpoint_size.h"
#include "util/rational.h"
#include "util/roundingmode.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

class FloatingPointLiteral
{
 public:
  /**
   * The kind of floating-point special constants that can be created via the
   * corresponding constructor.
   * These are prefixed with FP because of name clashes with NAN.
   */
  enum SpecialConstKind
  {
    FPINF,   // +-oo
    FPNAN,   // NaN
    FPZERO,  // +-zero
  };

  /**
   * Get the number of exponent bits in the unpacked format corresponding to a
   * given packed format.  This is the unpacked counter-part of
   * FloatingPointSize::exponentWidth().
   */
  static uint32_t getUnpackedExponentWidth(FloatingPointSize& size);
  /**
   * Get the number of exponent bits in the unpacked format corresponding to a
   * given packed format.  This is the unpacked counter-part of
   * FloatingPointSize::significandWidth().
   */
  static uint32_t getUnpackedSignificandWidth(FloatingPointSize& size);

  /**
   * Create a FP literal from its IEEE bit-vector representation.
   * @param exp_size The exponent size.
   * @param sig_size The significand size.
   * @param The bit-vector representation.
   */
  static std::unique_ptr<FloatingPointLiteral> create(uint32_t exp_size,
                                                      uint32_t sig_size,
                                                      const BitVector& bv);
  /**
   * Create a FP literal from its IEEE bit-vector representation.
   * @param size The floating-point format.
   * @param The bit-vector representation.
   */
  static std::unique_ptr<FloatingPointLiteral> create(
      const FloatingPointSize& size, const BitVector& bv);

  /**
   * Create a FP literal that represents a special constant.
   * @param size The floating-point format.
   * @param kind The special constant kind.
   */
  static std::unique_ptr<FloatingPointLiteral> create(
      const FloatingPointSize& size, SpecialConstKind kind);
  /**
   * Create a FP literal that represents a special constant.
   * @param size The floating-point format.
   * @param kind The special constant kind.
   */
  static std::unique_ptr<FloatingPointLiteral> create(
      const FloatingPointSize& size, SpecialConstKind kind, bool sign);

  /**
   * Create a FP literal from a signed or unsigned bit-vector value with
   * respect to given rounding mode.
   */
  static std::unique_ptr<FloatingPointLiteral> create(
      const FloatingPointSize& size,
      const RoundingMode& rm,
      const BitVector& bv,
      bool signedBV);

  /**
   * Create a FP literal from a rational value with respect to given rounding
   * mode.
   */
  static std::unique_ptr<FloatingPointLiteral> createFromRational(
      const FloatingPointSize& size, const RoundingMode& rm, const Rational& r);

  /**
   * Constructor.
   * @param exp_size The exponent size.
   * @param sig_size The significand size.
   */
  FloatingPointLiteral(uint32_t exp_size, uint32_t sig_size)
      : d_fp_size(exp_size, sig_size)
  {
  }
  /**
   * Constructor.
   * @param size The floating-point format.
   */
  FloatingPointLiteral(const FloatingPointSize& size) : d_fp_size(size) {}

  /** Destructor. */
  virtual ~FloatingPointLiteral();

  /** Clone this literal (polymorphic copy). */
  virtual std::unique_ptr<FloatingPointLiteral> clone() const = 0;

  /** @return The packed (IEEE-754) representation of this literal. */
  virtual BitVector pack() const = 0;

  /** @return The absolute value of this floating-point. */
  virtual std::unique_ptr<FloatingPointLiteral> absolute() const = 0;
  /** @return The negation of this floating-point. */
  virtual std::unique_ptr<FloatingPointLiteral> negate() const = 0;
  /**
   * Floating-point addition.
   * @param rm  The rounding mode.
   * @param arg The floating-point to add to this.
   * @return The floating-point addition of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> add(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const = 0;
  /**
   * Floating-point subtraction.
   * @param rm  The rounding mode.
   * @param arg The floating-point to subtract from this.
   * @return The floating-point subtraction of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> sub(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const = 0;
  /**
   * Floating-point multiplication.
   * @param rm  The rounding mode.
   * @param arg The floating-point to multiply with this.
   * @return The floating-point multiplication of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> mult(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const = 0;
  /**
   * Floating-point division.
   * @param rm  The rounding mode.
   * @param arg The floating-point to divide this by.
   * @return The floating-point division of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> div(
      const RoundingMode& rm, const FloatingPointLiteral& arg) const = 0;
  /**
   * Floating-point fused multiplication and addition.
   * @param rm   The rounding mode.
   * @param arg1 The floating-point to multiply to this.
   * @param arg2 The floating-point to add to the multiplication.
   * @return The floating-point fused multiplication and addition result.
   */
  virtual std::unique_ptr<FloatingPointLiteral> fma(
      const RoundingMode& rm,
      const FloatingPointLiteral& arg1,
      const FloatingPointLiteral& arg2) const = 0;
  /**
   * Floating-point square root.
   * @param rm The rounding mode.
   * @return The floating-point sqare root of this.
   */
  virtual std::unique_ptr<FloatingPointLiteral> sqrt(
      const RoundingMode& rm) const = 0;
  /**
   * Floating-point round to integral.
   * @param rm The rounding mode.
   * @return The floating-point round-to-integral of this.
   */
  virtual std::unique_ptr<FloatingPointLiteral> rti(
      const RoundingMode& rm) const = 0;
  /**
   * Floating-point remainder.
   * @param arg The floating-point to divide this by.
   * @return The floating-point remainder of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> rem(
      const FloatingPointLiteral& arg) const = 0;

  /**
   * Floating-point max (total version).
   * @param arg      The floating-point to compare this with.
   * @param zeroCase True to return the left (rather than the right operand) in
   *                 case of max(-0,+0) or max(+0,-0).
   * @return The floating-point max of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> maxTotal(
      const FloatingPointLiteral& arg, bool zeroCaseLeft) const = 0;
  /**
   * Floating-point min (total version).
   * @param arg      The floating-point to compare this with.
   * @param zeroCase True to return the left (rather than the right operand) in
   *                 case of min(-0,+0) or min(+0,-0).
   * @return The floating-point min of this and `arg`.
   */
  virtual std::unique_ptr<FloatingPointLiteral> minTotal(
      const FloatingPointLiteral& arg, bool zeroCaseLeft) const = 0;

  /** Equality (NOT: fp.eq but =) over floating-point values. */
  virtual bool operator==(const FloatingPointLiteral& fp) const = 0;
  /** Floating-point less or equal than. */
  virtual bool operator<=(const FloatingPointLiteral& arg) const = 0;
  /** Floating-point less than. */
  virtual bool operator<(const FloatingPointLiteral& arg) const = 0;

  /**
   * Get the unpacked representation of the exponent (as used by SymFPU) of this
   * floating-point value.
   * @note This is only required for constant-folding of floating-point variable
   *       components, as required by model generation (see #1915).
   */
  virtual BitVector getUnpackedExponent() const = 0;
  /**
   * Get the unpacked representation of the significand (as used by SymFPU) of
   * this floating-point value.
   * @note This is only required for constant-folding of floating-point variable
   *       components, as required by model generation (see #1915).
   */
  virtual BitVector getUnpackedSignificand() const = 0;
  /** True if this value is a negative value. */
  virtual bool getSign() const = 0;

  /** Return true if this represents a normal value. */
  virtual bool isNormal() const = 0;
  /** Return true if this represents a subnormal value. */
  virtual bool isSubnormal() const = 0;
  /** Return true if this represents a zero value. */
  virtual bool isZero() const = 0;
  /** Return true if this represents an infinite value. */
  virtual bool isInfinite() const = 0;
  /** Return true if this represents a NaN value. */
  virtual bool isNaN() const = 0;
  /** Return true if this represents a negative value. */
  virtual bool isNegative() const = 0;
  /** Return true if this represents a positive value. */
  virtual bool isPositive() const = 0;

  /**
   * Convert this floating-point to a floating-point of given size, with
   * respect to given rounding mode.
   */
  virtual std::unique_ptr<FloatingPointLiteral> convert(
      const FloatingPointSize& target, const RoundingMode& rm) const = 0;

  /**
   * Convert this floating-point to a signed bit-vector of given size,
   * with respect to given rounding mode (total version).
   * @param width The size of the target bit-vector.
   * @param rm    The rounding mode.
   * @returns The converted result, and `undefinedCase` in the undefined case.
   */
  virtual BitVector convertToSBVTotal(BitVectorSize width,
                                      const RoundingMode& rm,
                                      BitVector undefinedCase) const = 0;
  /**
   * Convert this floating-point to an unsigned bit-vector of given
   * size, with respect to given rounding mode (total version).
   * @param width The size of the target bit-vector.
   * @param rm    The rounding mode.
   * @returns The converted result, and `undefinedCase` in the undefined case.
   */
  virtual BitVector convertToUBVTotal(BitVectorSize width,
                                      const RoundingMode& rm,
                                      BitVector undefinedCase) const = 0;

  /**
   * Convert this floating-point to a rational.
   * @returns A pair of Rational and bool. The boolean flag is true if the
   *          result is defined (i.e., the value is not NaN or infinite), and
   *          false otherwise.
   */
  virtual std::pair<Rational, bool> convertToRational() const = 0;

  /** Return the size of this floating-point. */
  const FloatingPointSize& getSize() const { return d_fp_size; };

 protected:
  /** The floating-point size of this floating-point literal. */
  FloatingPointSize d_fp_size;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc5::internal
#endif
