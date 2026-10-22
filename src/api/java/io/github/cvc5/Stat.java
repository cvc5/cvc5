/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import static java.lang.foreign.ValueLayout.ADDRESS;
import static java.lang.foreign.ValueLayout.JAVA_LONG;

import io.github.cvc5.capi.CApi;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.util.HashMap;
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
  Stat(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, Stat::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_stat_release(pointer);
  }

  // endregion

  /**
   * @return A string representation of this Stat.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_stat_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * Is this value intended for internal use only?
   * @return Whether this is an internal statistic.
   */
  public boolean isInternal()
  {
    return isInternal(handle());
  }

  private boolean isInternal(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_is_internal(pointer));
  }

  /**
   * Does this value hold the default value?
   * @return Whether this is a defaulted statistic.
   */
  public boolean isDefault()
  {
    return isDefault(handle());
  }

  private boolean isDefault(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_is_default(pointer));
  }

  /**
   * Is this value an integer?
   * @return Whether the value is an integer.
   */
  public boolean isInt()
  {
    return isInt(handle());
  }

  private boolean isInt(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_is_int(pointer));
  }

  /**
   * Return the integer value.
   * @return The integer value.
   */
  public long getInt()
  {
    return getInt(handle());
  }

  private long getInt(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_get_int(pointer));
  }

  /**
   * Is this value a double?
   * @return Whether the value is a double.
   */
  public boolean isDouble()
  {
    return isDouble(handle());
  }

  private boolean isDouble(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_is_double(pointer));
  }

  /**
   * Return the double value.
   * @return The double value.
   */
  public double getDouble()
  {
    return getDouble(handle());
  }

  private double getDouble(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_get_double(pointer));
  }

  /**
   * Is this value a string?
   * @return Whether the value is a string.
   */
  public boolean isString()
  {
    return isString(handle());
  }

  private boolean isString(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_is_string(pointer));
  }

  /**
   * Return the string value.
   * @return The string value.
   */
  public String getString()
  {
    return getString(handle());
  }

  private String getString(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_stat_get_string(pointer));
  }

  /**
   * Is this value a histogram?
   * @return Whether the value is a histogram.
   */
  public boolean isHistogram()
  {
    return isHistogram(handle());
  }

  private boolean isHistogram(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_stat_is_histogram(pointer));
  }

  /**
   * Return the histogram value.
   * @return The histogram value.
   */
  public Map<String, Long> getHistogram()
  {
    return getHistogram(handle());
  }

  private Map<String, Long> getHistogram(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment keys = arena.allocate(ADDRESS);
      MemorySegment values = arena.allocate(ADDRESS);
      MemorySegment size = arena.allocate(JAVA_LONG);
      CApi.cvc5_stat_get_histogram(pointer, keys, values, size);
      Native.check();
      long n = size.get(JAVA_LONG, 0);
      String[] names = Native.strings(keys.get(ADDRESS, 0), n);
      // uint64_t values, as the same bits in a long (like the JNI implementation)
      long[] counts = Native.longs(values.get(ADDRESS, 0), n);
      Map<String, Long> histogram = new HashMap<>();
      for (int i = 0; i < names.length; i++)
      {
        histogram.put(names[i], counts[i]);
      }
      return histogram;
    }
  }
}
