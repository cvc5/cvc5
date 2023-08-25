/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
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

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * A cvc5 datatype.
 */
public class Datatype extends AbstractPointer implements Iterable<DatatypeConstructor>
{
  // region construction and destruction
  Datatype(long pointer)
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
   * Get the datatype constructor at a given index.
   * @param idx The index of the datatype constructor to return.
   * @return The datatype constructor with the given index.
   */
  public DatatypeConstructor getConstructor(int idx)
  {
    long constructorPointer = getConstructor(pointer, idx);
    return new DatatypeConstructor(constructorPointer);
  }

  private native long getConstructor(long pointer, int index);

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors, so in case of multiple,
   * similarly-named constructors, the first is returned.
   * @param name The name of the datatype constructor.
   * @return The datatype constructor with the given name.
   */
  public DatatypeConstructor getConstructor(String name)
  {
    long constructorPointer = getConstructor(pointer, name);
    return new DatatypeConstructor(constructorPointer);
  }

  private native long getConstructor(long pointer, String name);

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors and their selectors, so
   * in case of multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The datatype selector with the given name.
   */
  public DatatypeSelector getSelector(String name)
  {
    long selectorPointer = getSelector(pointer, name);
    return new DatatypeSelector(selectorPointer);
  }

  private native long getSelector(long pointer, String name);

  /** @return The name of this Datatype. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

  /** @return The number of constructors for this Datatype. */
  public int getNumConstructors()
  {
    return getNumConstructors(pointer);
  }

  private native int getNumConstructors(long pointer);

  /**
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The parameters of this datatype, if it is parametric. An exception.
   * is thrown if this datatype is not parametric.
   */
  public Sort[] getParameters()
  {
    long[] sortPointers = getParameters(pointer);
    Sort[] sorts = Utils.getSorts(sortPointers);
    return sorts;
  }

  private native long[] getParameters(long pointer);

  /**
   * @api.note This method is experimental and may change in future versions.
   *
   * @return True if this datatype is parametric.
   */
  public boolean isParametric()
  {
    return isParametric(pointer);
  }

  private native boolean isParametric(long pointer);

  /** @return True if this datatype corresponds to a co-datatype */
  public boolean isCodatatype()
  {
    return isCodatatype(pointer);
  }

  private native boolean isCodatatype(long pointer);

  /** @return True if this datatype corresponds to a tuple */
  public boolean isTuple()
  {
    return isTuple(pointer);
  }

  private native boolean isTuple(long pointer);

  /**
   * @api.note This method is experimental and may change in future versions.
   *
   * @return True if this datatype corresponds to a record.
   */
  public boolean isRecord()
  {
    return isRecord(pointer);
  }

  private native boolean isRecord(long pointer);

  /** @return True if this datatype is finite */
  public boolean isFinite()
  {
    return isFinite(pointer);
  }

  private native boolean isFinite(long pointer);

  /**
   * Is this datatype well-founded? If this datatype is not a codatatype,
   * this returns false if there are no values of this datatype that are of
   * finite size.
   *
   * @return True if this datatype is well-founded.
   */
  public boolean isWellFounded()
  {
    return isWellFounded(pointer);
  }

  private native boolean isWellFounded(long pointer);

  /**
   * @return True if this Datatype is a null object.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return A string representation of this datatype.
   */
  protected native String toString(long pointer);

  public class ConstIterator implements Iterator<DatatypeConstructor>
  {
    private int currentIndex;
    private int size;

    public ConstIterator()
    {
      currentIndex = -1;
      size = getNumConstructors();
    }

    @Override
    public boolean hasNext()
    {
      return currentIndex < size - 1;
    }

    @Override
    public DatatypeConstructor next()
    {
      if (currentIndex >= size - 1)
      {
        throw new NoSuchElementException();
      }
      currentIndex++;

      return getConstructor(currentIndex);
    }
  }

  @Override
  public Iterator<DatatypeConstructor> iterator()
  {
    return new ConstIterator();
  }
}
