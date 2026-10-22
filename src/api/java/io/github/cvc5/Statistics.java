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
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * Represents a snapshot of the solver statistics.
 */
public class Statistics extends AbstractPointer implements Iterable<Map.Entry<String, Stat>>
{
  // region construction and destruction
  Statistics(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, Statistics::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_stats_release(pointer);
  }

  // endregion

  /**
   * @return A string representation of this Statistics.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_stats_to_string(pointer));
  }

  /**
   * Retrieve the statistic with the given name.
   * Asserts that a statistic with the given name actually exists and throws
   * a {@code CVC5ApiRecoverableException} if it does not.
   * @param name Name of the statistic.
   * @return The statistic with the given name.
   */
  public Stat get(String name)
  {
    long statPointer = get(getPointer(), name);
    return new Stat(ctx, statPointer);
  }

  private long get(long pointer, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return CApi.cvc5_stats_get(pointer, Native.cstring(arena, name));
    }
  }

  /**
   * Begin iteration over the statistics values.
   * By default, only entries that are public (non-internal) and have been set
   * are visible while the others are skipped.
   * @param internal If set to true, internal statistics are shown as well.
   * @param defaulted If set to true, defaulted statistics are shown as well.
   */

  /**
   * Get the names and the native pointers of the statistics visited by an
   * iterator over this object.
   *
   * <p>The C API supports only one iteration at a time per statistics
   * object, so the iteration is completed here, in one go.</p>
   *
   * @param pointer The native pointer of this object.
   * @param internal Whether to visit internal statistics.
   * @param defaulted Whether to visit statistics that still have their
   *                  default value.
   * @return The names and the native pointers of the statistics. Ownership of
   *         the latter is transferred to the caller.
   */
  private Pair<String[], long[]> getEntries(long pointer, boolean internal, boolean defaulted)
  {
    List<String> names = new ArrayList<>();
    long[] stats = new long[16];
    int size = 0;
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment name = Native.outLong(arena);
      CApi.cvc5_stats_iter_init(pointer, internal, defaulted);
      while (CApi.cvc5_stats_iter_has_next(pointer))
      {
        long stat = CApi.cvc5_stats_iter_next(pointer, name.address());
        if (size == stats.length)
        {
          stats = Arrays.copyOf(stats, 2 * size);
        }
        stats[size++] = stat;
        names.add(Native.string(name.get(JAVA_LONG, 0)));
      }
    }
    return new Pair<>(names.toArray(new String[0]), Arrays.copyOf(stats, size));
  }

  /**
   * An iterator over the statistics entries maintained by the {@code Statistics} class.
   * This is a constant (read-only) iterator that returns immutable key-value pairs,
   * where the key is a {@code String} and the value is a {@code Stat}.
   *
   * <p>Since a {@code Statistics} object is a snapshot, the iterator fetches
   * all its entries when it is created and keeps no native state.</p>
   */
  public class ConstIterator implements Iterator<Map.Entry<String, Stat>>
  {
    private final String[] d_names;
    private final Stat[] d_stats;
    private int d_index = 0;

    /**
     * Constructs a new iterator over the statistics with specific filtering options.
     *
     * @param internal If {@code true}, internal statistics are included in the iteration.
     * @param defaulted If {@code true}, statistics that have default values are included.
     */
    public ConstIterator(boolean internal, boolean defaulted)
    {
      Pair<String[], long[]> entries = getEntries(getPointer(), internal, defaulted);
      d_names = entries.first;
      d_stats = new Stat[entries.second.length];
      for (int i = 0; i < d_stats.length; i++)
      {
        d_stats[i] = new Stat(ctx, entries.second[i]);
      }
    }

    /**
     * Constructs a new iterator over the statistics using default visibility options.
     * By default, only public (non-internal) and explicitly set statistics are shown.
     */
    public ConstIterator()
    {
      // the defaults of Statistics::begin() in the C++ API
      this(false, false);
    }

    @Override
    public boolean hasNext()
    {
      return d_index < d_names.length;
    }

    @Override
    public Map.Entry<String, Stat> next()
    {
      if (!hasNext())
      {
        throw new NoSuchElementException("Reached the end of the statistics");
      }
      Map.Entry<String, Stat> entry =
          new AbstractMap.SimpleImmutableEntry<>(d_names[d_index], d_stats[d_index]);
      d_index++;
      return entry;
    }
  }

  /**
   * Begin iteration over the statistics values.
   * By default, only entries that are public (non-internal) and have been set
   * are visible while the others are skipped.
   *
   * @param internal If set to {@code true}, internal statistics are shown as well.
   * @param defaulted If set to {@code true}, defaulted statistics are shown as well.
   * @return A {@code ConstIterator} over the matching statistics entries.
   */
  public ConstIterator iterator(boolean internal, boolean defaulted)
  {
    return new ConstIterator(internal, defaulted);
  }
  @Override
  public ConstIterator iterator()
  {
    return new ConstIterator();
  }
}
