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

import java.util.Iterator;
import java.util.NoSuchElementException;

public class Statistics extends AbstractPointer implements Iterable<Pair<String, Stat>>
{
  // region construction and destruction
  Statistics(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /**
   * @return a string representation of this Statistics
   */
  protected native String toString(long pointer);

  /**
   * Retrieve the statistic with the given name.
   * Asserts that a statistic with the given name actually exists and throws
   * a `CVC5ApiRecoverableException` if it does not.
   * @param name Name of the statistic.
   * @return The statistic with the given name.
   */
  public Stat get(String name)
  {
    long statPointer = get(pointer, name);
    return new Stat(solver, statPointer);
  }

  private native long get(long pointer, String name);

  /**
   * Begin iteration over the statistics values.
   * By default, only entries that are public (non-expert) and have been set
   * are visible while the others are skipped.
   * @param expert If set to true, expert statistics are shown as well.
   * @param defaulted If set to true, defaulted statistics are shown as well.
   */

  private native long getIterator(long pointer);

  private native boolean hasNext(long pointer, long iteratorPointer);

  private native Pair<String, Long> getNext(long pointer, long iteratorPointer)
      throws CVC5ApiException;

  private native long increment(long pointer, long iteratorPointer) throws CVC5ApiException;

  private native void deleteIteratorPointer(long iteratorPointer);

  public class ConstIterator implements Iterator<Pair<String, Stat>>
  {
    private long iteratorPointer = 0;

    public ConstIterator()
    {
      iteratorPointer = getIterator(pointer);
    }

    @Override public boolean hasNext()
    {
      return Statistics.this.hasNext(pointer, iteratorPointer);
    }

    @Override public Pair<String, Stat> next()
    {
      try
      {
        Pair<String, Long> pair = Statistics.this.getNext(pointer, iteratorPointer);
        Stat stat = new Stat(solver, pair.second);
        this.iteratorPointer = Statistics.this.increment(pointer, iteratorPointer);
        return new Pair<>(pair.first, stat);
      }
      catch (CVC5ApiException e)
      {
        throw new NoSuchElementException(e.getMessage());
      }
    }

    @Override public void finalize()
    {
      deleteIteratorPointer(iteratorPointer);
    }
  }

  @Override public Iterator<Pair<String, Stat>> iterator()
  {
    return new ConstIterator();
  }
};
