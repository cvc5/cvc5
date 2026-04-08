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
#include "util/floatingpoint_literal_symfpu_traits.h"
#include "util/floatingpoint_size.h"
#include "util/roundingmode.h"

/* -------------------------------------------------------------------------- */

namespace cvc5::internal {

using SymFPUUnpackedFloatLiteral =
    ::symfpu::unpackedFloat<symfpuLiteral::traits>;

class FloatingPointLiteralSymFPU
{
  friend class FloatingPoint;

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

  /** Constructors. */

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

  ~FloatingPointLiteralSymFPU() {}

  /** Return the size of this FP literal. */
  const FloatingPointSize& getSize() const { return d_fp_size; };

  /** Return the packed (IEEE-754) representation of this literal. */
  BitVector pack(void) const;

  /** Floating-point absolute value literal. */
  FloatingPointLiteralSymFPU absolute(void) const;
  /** Floating-point negation literal. */
  FloatingPointLiteralSymFPU negate(void) const;
  /** Floating-point addition literal. */
  FloatingPointLiteralSymFPU add(const RoundingMode& rm,
                                 const FloatingPointLiteralSymFPU& arg) const;
  /** Floating-point subtraction literal. */
  FloatingPointLiteralSymFPU sub(const RoundingMode& rm,
                                 const FloatingPointLiteralSymFPU& arg) const;
  /** Floating-point multiplication literal. */
  FloatingPointLiteralSymFPU mult(const RoundingMode& rm,
                                  const FloatingPointLiteralSymFPU& arg) const;
  /** Floating-point division literal. */
  FloatingPointLiteralSymFPU div(const RoundingMode& rm,
                                 const FloatingPointLiteralSymFPU& arg) const;
  /** Floating-point fused multiplication and addition literal. */
  FloatingPointLiteralSymFPU fma(const RoundingMode& rm,
                                 const FloatingPointLiteralSymFPU& arg1,
                                 const FloatingPointLiteralSymFPU& arg2) const;
  /** Floating-point square root literal. */
  FloatingPointLiteralSymFPU sqrt(const RoundingMode& rm) const;
  /** Floating-point round to integral literal. */
  FloatingPointLiteralSymFPU rti(const RoundingMode& rm) const;
  /** Floating-point remainder literal. */
  FloatingPointLiteralSymFPU rem(const FloatingPointLiteralSymFPU& arg) const;

  /**
   * Floating-point max literal (total version).
   * zeroCase: true to return the left (rather than the right operand) in case
   *           of max(-0,+0) or max(+0,-0).
   */
  FloatingPointLiteralSymFPU maxTotal(const FloatingPointLiteralSymFPU& arg,
                                      bool zeroCaseLeft) const;
  /**
   * Floating-point min literal (total version).
   * zeroCase: true to return the left (rather than the right operand) in case
   *           of min(-0,+0) or min(+0,-0).
   */
  FloatingPointLiteralSymFPU minTotal(const FloatingPointLiteralSymFPU& arg,
                                      bool zeroCaseLeft) const;

  /** Equality literal (NOT: fp.eq but =) over floating-point values. */
  bool operator==(const FloatingPointLiteralSymFPU& fp) const;
  /** Floating-point less or equal than literal. */
  bool operator<=(const FloatingPointLiteralSymFPU& arg) const;
  /** Floating-point less than literal. */
  bool operator<(const FloatingPointLiteralSymFPU& arg) const;

  /** Get the exponent of this floating-point value. */
  BitVector getExponent() const;
  /** Get the significand of this floating-point value. */
  BitVector getSignificand() const;
  /** True if this value is a negative value. */
  bool getSign() const;

  /** Return true if this literal represents a normal value. */
  bool isNormal(void) const;
  /** Return true if this  literal represents a subnormal value. */
  bool isSubnormal(void) const;
  /** Return true if this literal represents a zero value. */
  bool isZero(void) const;
  /** Return true if this literal represents an infinite value. */
  bool isInfinite(void) const;
  /** Return true if this literal represents a NaN value. */
  bool isNaN(void) const;
  /** Return true if this literal represents a negative value. */
  bool isNegative(void) const;
  /** Return true if this literal represents a positive value. */
  bool isPositive(void) const;

  /**
   * Convert this floating-point literal to a literal of given size, with
   * respect to given rounding mode.
   */
  FloatingPointLiteralSymFPU convert(const FloatingPointSize& target,
                                     const RoundingMode& rm) const;

  /**
   * Convert this floating-point literal to a signed bit-vector of given size,
   * with respect to given rounding mode (total version).
   * Returns given bit-vector 'undefinedCase' in the undefined case.
   */
  BitVector convertToSBVTotal(BitVectorSize width,
                              const RoundingMode& rm,
                              BitVector undefinedCase) const;
  /**
   * Convert this floating-point literal to an unsigned bit-vector of given
   * size, with respect to given rounding mode (total version).
   * Returns given bit-vector 'undefinedCase' in the undefined case.
   */
  BitVector convertToUBVTotal(BitVectorSize width,
                              const RoundingMode& rm,
                              BitVector undefinedCase) const;
  /** Return wrapped floating-point literal. */
  const SymFPUUnpackedFloatLiteral& getSymUF() const { return d_symuf; }

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
      : d_fp_size(size), d_symuf(SymFPUUnpackedFloatLiteral(sign, exp, sig))
  {
  }

  /** Create a FP literal from a symFPU unpacked float. */
  FloatingPointLiteralSymFPU(const FloatingPointSize& size,
                             SymFPUUnpackedFloatLiteral symuf)
      : d_fp_size(size), d_symuf(symuf) {};

  /** The floating-point size of this floating-point literal. */
  FloatingPointSize d_fp_size;
  /** The actual floating-point value, a SymFPU unpackedFloat. */
  SymFPUUnpackedFloatLiteral d_symuf;
};

/* -------------------------------------------------------------------------- */

}  // namespace cvc5::internal

#endif
