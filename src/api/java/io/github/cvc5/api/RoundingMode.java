/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Abdalrhman Mohamed, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5.api;

public enum RoundingMode {
  /**
   * Round to the nearest even number.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with an even least
   * significant digit will be delivered.
   */
  ROUND_NEAREST_TIES_TO_EVEN(0),
  /**
   * Round towards positive infinity (+oo).
   * The result shall be the format's floating-point number (possibly +oo)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_POSITIVE(1),
  /**
   * Round towards negative infinity (-oo).
   * The result shall be the format's floating-point number (possibly -oo)
   * closest to and no less than the infinitely precise result.
   */
  ROUND_TOWARD_NEGATIVE(2),
  /**
   * Round towards zero.
   * The result shall be the format's floating-point number closest to and no
   * greater in magnitude than the infinitely precise result.
   */
  ROUND_TOWARD_ZERO(3),
  /**
   * Round to the nearest number away from zero.
   * If the two nearest floating-point numbers bracketing an unrepresentable
   * infinitely precise result are equally near, the one with larger magnitude
   * will be selected.
   */
  ROUND_NEAREST_TIES_TO_AWAY(4);

  private int value;

  private RoundingMode(int value)
  {
    this.value = value;
  }

  public int getValue()
  {
    return value;
  }
}
