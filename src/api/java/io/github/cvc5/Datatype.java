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

import io.github.cvc5.capi.CApi;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * A cvc5 datatype.
 */
public class Datatype extends AbstractPointer implements Iterable<DatatypeConstructor>
{
  // region construction and destruction
  Datatype(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, Datatype::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_dt_release(pointer);
  }

  // endregion

  /**
   * Syntactic equality operator.
   *
   * @param dt The datatype to compare to for equality.
   * @return True if the datatypes are equal.
   */
  @Override
  public boolean equals(Object dt)
  {
    if (this == dt)
    {
      return true;
    }
    if (dt == null || getClass() != dt.getClass())
    {
      return false;
    }
    Datatype datatype = (Datatype) dt;
    if (address() == datatype.address())
    {
      return true;
    }
    return equals(handle(), datatype.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_dt_is_equal(pointer1, pointer2));
  }

  /**
   * Get the datatype constructor at a given index.
   * @param idx The index of the datatype constructor to return.
   * @return The datatype constructor with the given index.
   */
  public DatatypeConstructor getConstructor(int idx)
  {
    MemorySegment constructorPointer = getConstructor(handle(), idx);
    return new DatatypeConstructor(ctx, constructorPointer);
  }

  private MemorySegment getConstructor(MemorySegment pointer, int index)
  {
    return Native.handle(CApi.cvc5_dt_get_constructor(pointer, index));
  }

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors, so in case of multiple,
   * similarly-named constructors, the first is returned.
   * @param name The name of the datatype constructor.
   * @return The datatype constructor with the given name.
   */
  public DatatypeConstructor getConstructor(String name)
  {
    MemorySegment constructorPointer = getConstructor(handle(), name);
    return new DatatypeConstructor(ctx, constructorPointer);
  }

  private MemorySegment getConstructor(MemorySegment pointer, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_dt_get_constructor_by_name(pointer, arena.allocateFrom(name)));
    }
  }

  /**
   * Get the datatype constructor with the given name.
   * This is a linear search through the constructors and their selectors, so
   * in case of multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The datatype selector with the given name.
   */
  public DatatypeSelector getSelector(String name)
  {
    MemorySegment selectorPointer = getSelector(handle(), name);
    return new DatatypeSelector(ctx, selectorPointer);
  }

  private MemorySegment getSelector(MemorySegment pointer, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_dt_get_selector(pointer, arena.allocateFrom(name)));
    }
  }

  /**
   * Get the name of this Datatype.
   *
   * @return The name of this Datatype.
   */
  public String getName()
  {
    return getName(handle());
  }

  private String getName(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_dt_get_name(pointer));
  }

  /**
   * Get the number of constructors for this Datatype.
   *
   * @return The number of constructors for this Datatype.
   */
  public int getNumConstructors()
  {
    return getNumConstructors(handle());
  }

  private int getNumConstructors(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_dt_get_num_constructors(pointer));
  }

  /**
   * Get the parameters of this datatype.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The parameters of this datatype, if it is parametric. An exception.
   * is thrown if this datatype is not parametric.
   */
  public Sort[] getParameters()
  {
    MemorySegment[] sortPointers = getParameters(handle());
    Sort[] sorts = Utils.getSorts(ctx, sortPointers);
    return sorts;
  }

  private MemorySegment[] getParameters(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment sorts = Native.check(CApi.cvc5_dt_get_parameters(pointer, size));
      return Native.handles(sorts, size.get(JAVA_LONG, 0));
    }
  }

  /**
   * Determine if this datatype is parametric.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return True if this datatype is parametric.
   */
  public boolean isParametric()
  {
    return isParametric(handle());
  }

  private boolean isParametric(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_is_parametric(pointer));
  }

  /**
   * Determine if this datatype corresponds to a co-datatype.
   *
   * @return True if this datatype corresponds to a co-datatype.
   */
  public boolean isCodatatype()
  {
    return isCodatatype(handle());
  }

  private boolean isCodatatype(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_is_codatatype(pointer));
  }

  /**
   * Determine if this datatype corresponds to a tuple.
   *
   * @return True if this datatype corresponds to a tuple.
   */
  public boolean isTuple()
  {
    return isTuple(handle());
  }

  private boolean isTuple(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_is_tuple(pointer));
  }

  /**
   * Determine if this datatype corresponds to a record.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return True if this datatype corresponds to a record.
   */
  public boolean isRecord()
  {
    return isRecord(handle());
  }

  private boolean isRecord(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_is_record(pointer));
  }

  /**
   * Determine if this datatype is finite.
   *
   * @return True if this datatype is finite
   */
  public boolean isFinite()
  {
    return isFinite(handle());
  }

  private boolean isFinite(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_is_finite(pointer));
  }

  /**
   * Is this datatype well-founded? If this datatype is not a codatatype,
   * this returns false if there are no values of this datatype that are of
   * finite size.
   *
   * @return True if this datatype is well-founded.
   */
  public boolean isWellFounded()
  {
    return isWellFounded(handle());
  }

  private boolean isWellFounded(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_dt_is_well_founded(pointer));
  }

  /**
   * Determine if this Datatype is a null object.
   *
   * @return True if this Datatype is a null object.
   */
  public boolean isNull()
  {
    return isNull(handle());
  }

  private boolean isNull(MemorySegment pointer)
  {
    return pointer.address() == 0;
  }

  /**
   * Provide a string representation of the native datatype.
   *
   * @param pointer The native memory address pointing to the datatype.
   * @return A string representation of this datatype.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_dt_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * ConstIterator is an implementation of the {@link Iterator} interface for iterating over
   * a collection of {@code DatatypeConstructor} objects.
   * It provides read-only access to the elements.
   */
  public class ConstIterator implements Iterator<DatatypeConstructor>
  {
    private int currentIndex;
    private int size;

    /**
     * Constructs a new ConstIterator.
     */
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

  /**
   * Get the hash value of a datatype.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(handle()));
  }

  private long hashCode(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      return 0;
    }
    return Native.check(CApi.cvc5_dt_hash(pointer));
  }
}
