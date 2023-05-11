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
 * The class representing a floating-point format.
 */
#include "cvc5_public.h"

#ifndef CVC5__FLOATINGPOINT_SIZE_H
#define CVC5__FLOATINGPOINT_SIZE_H

namespace cvc5::internal {

// Inline these!
inline bool validExponentSize(uint32_t e) { return e >= 2; }
inline bool validSignificandSize(uint32_t s) { return s >= 2; }

/**
 * Floating point sorts are parameterised by two constants > 1 giving the
 * width (in bits) of the exponent and significand (including the hidden bit).
 * So, IEEE-754 single precision, a.k.a. float, is described as 8 24.
 */
class FloatingPointSize
{
 public:
  /** Constructors. */
  FloatingPointSize(uint32_t exp_size, uint32_t sig_size);
  FloatingPointSize(const FloatingPointSize& old);

  /** Operator overload for equality comparison. */
  bool operator==(const FloatingPointSize& fps) const
  {
    return (d_exp_size == fps.d_exp_size) && (d_sig_size == fps.d_sig_size);
  }

  /** Implement the interface that symfpu uses for floating-point formats. */

  /** Get the exponent bit-width of this floating-point format. */
  inline uint32_t exponentWidth(void) const { return d_exp_size; }
  /** Get the significand bit-width of this floating-point format. */
  inline uint32_t significandWidth(void) const { return d_sig_size; }
  /**
   * Get the bit-width of the packed representation of this floating-point
   * format (= exponent + significand bit-width, convenience wrapper).
   */
  inline uint32_t packedWidth(void) const
  {
    return exponentWidth() + significandWidth();
  }
  /**
   * Get the exponent bit-width of the packed representation of this
   * floating-point format (= exponent bit-width).
   */
  inline uint32_t packedExponentWidth(void) const { return exponentWidth(); }
  /**
   * Get the significand bit-width of the packed representation of this
   * floating-point format (= significand bit-width - 1).
   */
  inline uint32_t packedSignificandWidth(void) const
  {
    return significandWidth() - 1;
  }

 private:
  /** Exponent bit-width. */
  uint32_t d_exp_size;
  /** Significand bit-width. */
  uint32_t d_sig_size;

}; /* class FloatingPointSize */

/**
 * Hash function for floating point formats.
 */
struct FloatingPointSizeHashFunction
{
  static inline size_t ROLL(size_t X, size_t N)
  {
    return (((X) << (N)) | ((X) >> (8 * sizeof((X)) - (N))));
  }

  inline size_t operator()(const FloatingPointSize& t) const
  {
    return size_t(ROLL(t.exponentWidth(), 4 * sizeof(uint32_t))
                  | t.significandWidth());
  }
}; /* struct FloatingPointSizeHashFunction */
}  // namespace cvc5::internal

#endif
