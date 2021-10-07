/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mudathir Mohamed
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

package cvc5;

/** Default value, current value, minimum and maximum of a numeric value */
public class NumberInfo<T> extends ValueInfo<T>
{
  private final T minimum;
  private final T maximum;
  public NumberInfo(T defaultValue, T currentValue, T minimum, T maximum)
  {
    super(defaultValue, currentValue);
    this.minimum = minimum;
    this.maximum = maximum;
  }
  public T getMinimum()
  {
    return minimum;
  }
  public T getMaximum()
  {
    return maximum;
  }
}