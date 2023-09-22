/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sampler class that generates random values of different sorts
 *
 * The Sampler class can be used to generate random values of different sorts
 * with biased and unbiased distributions.
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL_FLOATINGPOINT_SAMPLER_H
#define CVC5__UTIL_FLOATINGPOINT_SAMPLER_H

#include "util/floatingpoint.h"

namespace cvc5::internal {

class Sampler
{
 public:
  /**
   * Generates a random, uniform bit-vector value.
   */
  static BitVector pickBvUniform(unsigned sz);

  /**
   * Generates a random, uniform floating-point value.
   */
  static FloatingPoint pickFpUniform(unsigned e, unsigned s);

  /**
   * Generates a random floating-point value biased towards special values
   * (e.g.  +/- inf) and interesting bit-patterns (e.g. values with a zero
   * significand).
   */
  static FloatingPoint pickFpBiased(unsigned e, unsigned s);

 private:
  /**
   * Probablility with which special floating-point values are picked when
   * picking a biased floating-point value
   */
  static constexpr double probSpecial = 0.2;
};

}  // namespace cvc5::internal

#endif /* CVC5__UTIL_FLOATINGPOINT_SAMPLER_H */
