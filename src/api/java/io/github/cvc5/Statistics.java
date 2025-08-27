/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
  Statistics(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

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
    long statPointer = get(pointer, name);
    return new Stat(statPointer);
  }

  private native long get(long pointer, String name);

  /**
   * Begin iteration over the statistics values.
   * By default, only entries that are public (non-internal) and have been set
   * are visible while the others are skipped.
   * @param internal If set to true, internal statistics are shown as well.
   * @param defaulted If set to true, defaulted statistics are shown as well.
   */

  private native long getIteratorOpts(long pointer, boolean internal, boolean defaulted);
  private native long getIterator(long pointer);

  private native boolean hasNext(long pointer, long iteratorPointer);

  private native Pair<String, Long> getNext(long pointer, long iteratorPointer)
      throws CVC5ApiException;

  private native long increment(long pointer, long iteratorPointer) throws CVC5ApiException;

  private native void deleteIteratorPointer(long iteratorPointer);

  /**
   * An iterator over the statistics entries maintained by the {@code Statistics} class.
   * This is a constant (read-only) iterator that returns immutable key-value pairs,
   * where the key is a {@code String} and the value is a {@code Stat}.
   */
  public class ConstIterator implements Iterator<Map.Entry<String, Stat>>
  {
    private long iteratorPointer = 0;

    /**
     * Constructs a new iterator over the statistics with specific filtering options.
     *
     * @param internal If {@code true}, internal statistics are included in the iteration.
     * @param defaulted If {@code true}, statistics that have default values are included.
     */
    public ConstIterator(boolean internal, boolean defaulted)
    {
      iteratorPointer = getIteratorOpts(pointer, internal, defaulted);
    }
    /**
     * Constructs a new iterator over the statistics using default visibility options.
     * By default, only public (non-internal) and explicitly set statistics are shown.
     */
    public ConstIterator()
    {
      iteratorPointer = getIterator(pointer);
    }

    @Override
    public boolean hasNext()
    {
      return Statistics.this.hasNext(pointer, iteratorPointer);
    }

    @Override
    public Map.Entry<String, Stat> next()
    {
      try
      {
        Pair<String, Long> pair = Statistics.this.getNext(pointer, iteratorPointer);
        Stat stat = new Stat(pair.second);
        this.iteratorPointer = Statistics.this.increment(pointer, iteratorPointer);
        return new AbstractMap.SimpleImmutableEntry<>(pair.first, stat);
      }
      catch (CVC5ApiException e)
      {
        throw new NoSuchElementException(e.getMessage());
      }
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
