/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.util.Map;

/**
 * Represents a snapshot of a single statistic value.
 * A value can be of type {@code long}, {@code double}, {@code String} or a histogram
 * ({@code Map<String, Long>}).
 * The value type can be queried (using {@code isInt()}, {@code isDouble()}, etc.) and
 * the stored value can be accessed (using {@code getInt()}, {@code getDouble()}, etc.).
 * It is possible to query whether this statistic is an internal statistic by
 * {@code isInternal()} and whether its value is the default value by {@code isDefault()}.
 */
public class Stat extends AbstractPointer
{
  // region construction and destruction
  Stat(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /**
   * @return A string representation of this Stat.
   */
  protected native String toString(long pointer);

  /**
   * Is this value intended for internal use only?
   * @return Whether this is an internal statistic.
   */
  public boolean isInternal()
  {
    return isInternal(pointer);
  }

  private native boolean isInternal(long pointer);

  /**
   * Does this value hold the default value?
   * @return Whether this is a defaulted statistic.
   */
  public boolean isDefault()
  {
    return isDefault(pointer);
  }

  private native boolean isDefault(long pointer);

  /**
   * Is this value an integer?
   * @return Whether the value is an integer.
   */
  public boolean isInt()
  {
    return isInt(pointer);
  }

  private native boolean isInt(long pointer);

  /**
   * Return the integer value.
   * @return The integer value.
   */
  public long getInt()
  {
    return getInt(pointer);
  }

  private native long getInt(long pointer);

  /**
   * Is this value a double?
   * @return Whether the value is a double.
   */
  public boolean isDouble()
  {
    return isDouble(pointer);
  }

  private native boolean isDouble(long pointer);

  /**
   * Return the double value.
   * @return The double value.
   */
  public double getDouble()
  {
    return getDouble(pointer);
  }

  private native double getDouble(long pointer);

  /**
   * Is this value a string?
   * @return Whether the value is a string.
   */
  public boolean isString()
  {
    return isString(pointer);
  }

  private native boolean isString(long pointer);

  /**
   * Return the string value.
   * @return The string value.
   */
  public String getString()
  {
    return getString(pointer);
  }

  private native String getString(long pointer);

  /**
   * Is this value a histogram?
   * @return Whether the value is a histogram.
   */
  public boolean isHistogram()
  {
    return isHistogram(pointer);
  }

  private native boolean isHistogram(long pointer);

  /**
   * Return the histogram value.
   * @return The histogram value.
   */
  public Map<String, Long> getHistogram()
  {
    return getHistogram(pointer);
  }

  private native Map<String, Long> getHistogram(long pointer);
};
