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

import java.util.AbstractMap;
import java.util.Iterator;
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

  private static native void deletePointer(long pointer);

  // endregion

  /**
   * @return A string representation of this Statistics.
   */
  protected native String toString(long pointer);

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

  private native long get(long pointer, String name);

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
   * @param pointer The native pointer of this object.
   * @param internal Whether to visit internal statistics.
   * @param defaulted Whether to visit statistics that still have their
   *                  default value.
   * @return The names and the native pointers of the statistics. Ownership of
   *         the latter is transferred to the caller.
   */
  private native Pair<String[], long[]> getEntries(
      long pointer, boolean internal, boolean defaulted);

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
