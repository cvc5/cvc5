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

import static java.lang.foreign.ValueLayout.JAVA_LONG;

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
public class Stat extends AbstractPointer{// region construction and destruction
    Stat(NativeContext ctx, long pointer){super(ctx, pointer, Stat::deletePointer);
}

private static void deletePointer(long pointer)
{
  CApi.cvc5_stat_release(pointer);
}

// endregion

/**
 * @return A string representation of this Stat.
 */
protected String toString(long pointer)
{
  return Native.string(CApi.cvc5_stat_to_string(pointer));
}

/**
 * Is this value intended for internal use only?
 * @return Whether this is an internal statistic.
 */
public boolean isInternal()
{
  return isInternal(getPointer());
}

private boolean isInternal(long pointer)
{
  return CApi.cvc5_stat_is_internal(pointer);
}

/**
 * Does this value hold the default value?
 * @return Whether this is a defaulted statistic.
 */
public boolean isDefault()
{
  return isDefault(getPointer());
}

private boolean isDefault(long pointer)
{
  return CApi.cvc5_stat_is_default(pointer);
}

/**
 * Is this value an integer?
 * @return Whether the value is an integer.
 */
public boolean isInt()
{
  return isInt(getPointer());
}

private boolean isInt(long pointer)
{
  return CApi.cvc5_stat_is_int(pointer);
}

/**
 * Return the integer value.
 * @return The integer value.
 */
public long getInt()
{
  return getInt(getPointer());
}

private long getInt(long pointer)
{
  return CApi.cvc5_stat_get_int(pointer);
}

/**
 * Is this value a double?
 * @return Whether the value is a double.
 */
public boolean isDouble()
{
  return isDouble(getPointer());
}

private boolean isDouble(long pointer)
{
  return CApi.cvc5_stat_is_double(pointer);
}

/**
 * Return the double value.
 * @return The double value.
 */
public double getDouble()
{
  return getDouble(getPointer());
}

private double getDouble(long pointer)
{
  return CApi.cvc5_stat_get_double(pointer);
}

/**
 * Is this value a string?
 * @return Whether the value is a string.
 */
public boolean isString()
{
  return isString(getPointer());
}

private boolean isString(long pointer)
{
  return CApi.cvc5_stat_is_string(pointer);
}

/**
 * Return the string value.
 * @return The string value.
 */
public String getString()
{
  return getString(getPointer());
}

private String getString(long pointer)
{
  return Native.string(CApi.cvc5_stat_get_string(pointer));
}

/**
 * Is this value a histogram?
 * @return Whether the value is a histogram.
 */
public boolean isHistogram()
{
  return isHistogram(getPointer());
}

private boolean isHistogram(long pointer)
{
  return CApi.cvc5_stat_is_histogram(pointer);
}

/**
 * Return the histogram value.
 * @return The histogram value.
 */
public Map<String, Long> getHistogram()
{
  return getHistogram(getPointer());
}

private Map<String, Long> getHistogram(long pointer)
{
  try (Arena arena = Arena.ofConfined())
  {
    MemorySegment keys = Native.outLong(arena);
    MemorySegment values = Native.outLong(arena);
    MemorySegment size = Native.outLong(arena);
    CApi.cvc5_stat_get_histogram(pointer, keys.address(), values.address(), size.address());
    long n = size.get(JAVA_LONG, 0);
    String[] names = Native.strings(keys.get(JAVA_LONG, 0), n);
    // uint64_t values, as the same bits in a long (like the JNI implementation)
    long[] counts = Native.longs(values.get(JAVA_LONG, 0), n);
    Map<String, Long> histogram = new HashMap<>();
    for (int i = 0; i < names.length; i++)
    {
      histogram.put(names[i], counts[i]);
    }
    return histogram;
  }
}
}
;
