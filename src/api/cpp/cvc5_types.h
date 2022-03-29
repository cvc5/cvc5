/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common cvc5 types.
 */

#include "cvc5_export.h"

#ifndef CVC5__API__CVC5_TYPES_H
#define CVC5__API__CVC5_TYPES_H

namespace cvc5::api {

/**
 * Rounding modes for floating-point numbers.
 *
 * For many floating-point operations, infinitely precise results may not be
 * representable with the number of available bits. Thus, the results are
 * rounded in a certain way to one of the representable floating-point numbers.
 *
 * \verbatim embed:rst:leading-asterisk
 * These rounding modes directly follow the SMT-LIB theory for floating-point
 * arithmetic, which in turn is based on IEEE Standard 754 :cite:`IEEE754`.
 * The rounding modes are specified in Sections 4.3.1 and 4.3.2 of the IEEE
 * Standard 754.
 * \endverbatim
 */
enum RoundingMode
{
  /**
   * Round to the nearest even number.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   */
  ROUND_NEAREST_TIES_TO_EVEN,
  /**
   * Round towards positive infinity (+oo).
   * The result shall be the format's floating-point number (possibly +oo)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_POSITIVE,
  /**
   * Round towards negative infinity (-oo).
   * The result shall be the format's floating-point number (possibly -oo)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_NEGATIVE,
  /**
   * Round towards zero.
   * The result shall be the format's floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   */
  ROUND_TOWARD_ZERO,
  /**
   * Round to the nearest number away from zero.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   */
  ROUND_NEAREST_TIES_TO_AWAY,
};

}  // namespace cvc5::api

namespace cvc5::modes {

enum BlockModelsMode
{
  /** Block models based on the SAT skeleton. */
  LITERALS,
  /** Block models based on the concrete model values for the free variables. */
  VALUES
};

}

#endif
