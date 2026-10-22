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

import java.lang.foreign.Arena;
import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * A cvc5 datatype constructor.
 */
public class DatatypeConstructor extends AbstractPointer implements Iterable<DatatypeSelector>
{
  // region construction and destruction
  DatatypeConstructor(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, DatatypeConstructor::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_dt_cons_release(pointer);
  }

  // endregion

  /**
   * Syntactic equality operator.
   *
   * @param c The datatype constructor to compare to for equality.
   * @return True if the datatype constructors are equal.
   */
  @Override
  public boolean equals(Object c)
  {
    if (this == c)
    {
      return true;
    }
    if (c == null || getClass() != c.getClass())
    {
      return false;
    }
    DatatypeConstructor cons = (DatatypeConstructor) c;
    if (this.pointer == cons.pointer)
    {
      return true;
    }
    return equals(getPointer(), cons.getPointer());
  }

  private boolean equals(long pointer1, long pointer2)
  {
    return CApi.cvc5_dt_cons_is_equal(pointer1, pointer2);
  }

  /**
   * Get the name of this Datatype constructor.
   *
   * @return The name of this Datatype constructor.
   */
  public String getName()
  {
    return getName(getPointer());
  }

  private String getName(long pointer)
  {
    return Native.string(CApi.cvc5_dt_cons_get_name(pointer));
  }

  /**
   * Get the constructor term of this datatype constructor.
   *
   * Datatype constructors are a special class of function-like terms whose sort
   * is datatype constructor ({@link Sort#isDatatypeConstructor()}). All
   * datatype constructors, including nullary ones, should be used as the
   * first argument to Terms whose kind is {@link Kind#APPLY_CONSTRUCTOR}.
   * For example, the nil list is represented by the term
   * {@code (APPLY_CONSTRUCTOR nil)}, where {@code nil} is the term returned by
   * this method.
   *
   * @api.note This method should not be used for parametric datatypes. Instead,
   *           use method
   *           {@link DatatypeConstructor#getInstantiatedTerm(Sort)} below.
   *
   * @return The constructor term.
   */
  public Term getTerm()
  {
    long termPointer = getTerm(getPointer());
    return new Term(ctx, termPointer);
  }

  private long getTerm(long pointer)
  {
    return CApi.cvc5_dt_cons_get_term(pointer);
  }

  /**
   * Get the constructor term of this datatype constructor whose return
   * type is {@code retSort}.
   *
   * This method is intended to be used on constructors of parametric datatypes
   * and can be seen as returning the constructor term that has been explicitly
   * cast to the given sort.
   *
   * This method is required for constructors of parametric datatypes whose
   * return type cannot be determined by type inference. For example, given:
   *   {@code (declare-datatype List (par (T) ((nil) (cons (head T)
   *          (tail (List T))))))}
   * The type of nil terms need to be provided by the user. In SMT version 2.6,
   * this is done via the syntax for qualified identifiers:
   *   {@code (as nil (List Int))}
   * This method is equivalent of applying the above, where this
   * DatatypeConstructor is the one corresponding to {@code nil}, and
   * {@code retSort} is {@code (List Int)}.
   *
   * @api.note The returned constructor term {@code t} is used to construct the
   *           above (nullary) application of {@code nil} with
   *           {@code Solver.mkTerm(APPLY_CONSTRUCTOR, new Term[] {t})}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param retSort The desired return sort of the constructor.
   * @return The constructor term.
   */
  public Term getInstantiatedTerm(Sort retSort)
  {
    long termPointer = getInstantiatedTerm(getPointer(), retSort.getPointer());
    return new Term(ctx, termPointer);
  }

  private long getInstantiatedTerm(long pointer, long retSortPointer)
  {
    return CApi.cvc5_dt_cons_get_instantiated_term(pointer, retSortPointer);
  }

  /**
   * Get the tester term of this datatype constructor.
   *
   * Similar to constructors, testers are a class of function-like terms of
   * tester sort ({@link Sort#isDatatypeTester()}), and should be used as the
   * first argument of Terms of kind {@link Kind#APPLY_TESTER}.
   *
   * @return The tester term.
   */
  public Term getTesterTerm()
  {
    long termPointer = getTesterTerm(getPointer());
    return new Term(ctx, termPointer);
  }
  private long getTesterTerm(long pointer)
  {
    return CApi.cvc5_dt_cons_get_tester_term(pointer);
  }

  /**
   * Get the number of selectors (so far) of this Datatype constructor.
   *
   * @return The number of selectors (so far) of this Datatype constructor.
   */
  public int getNumSelectors()
  {
    return getNumSelectors(getPointer());
  }
  private int getNumSelectors(long pointer)
  {
    return (int) CApi.cvc5_dt_cons_get_num_selectors(pointer);
  }

  /**
   * Get the DatatypeSelector at the given index
   * @param index The given index i.
   * @return The i^th DatatypeSelector.
   */
  public DatatypeSelector getSelector(int index)
  {
    long selectorPointer = getSelector(getPointer(), index);
    return new DatatypeSelector(ctx, selectorPointer);
  }
  private long getSelector(long pointer, int index)
  {
    return CApi.cvc5_dt_cons_get_selector(pointer, index);
  }

  /**
   * Get the datatype selector with the given name.
   * This is a linear search through the selectors, so in case of
   * multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The first datatype selector with the given name.
   */
  public DatatypeSelector getSelector(String name)
  {
    long selectorPointer = getSelector(getPointer(), name);
    return new DatatypeSelector(ctx, selectorPointer);
  }
  private long getSelector(long pointer, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return CApi.cvc5_dt_cons_get_selector_by_name(pointer, Native.cstring(arena, name));
    }
  }

  /**
   * Determine if this DatatypeConstructor is a null object.
   *
   * @return True if this DatatypeConstructor is a null object.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private boolean isNull(long pointer)
  {
    return pointer == 0;
  }

  /**
   * Provide a string representation of the native datatype constructor.
   *
   * @param pointer The native memory address pointing to the datatype constructor.
   * @return A string representation of this datatype constructor.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_dt_cons_to_string(pointer));
  }

  /**
   * ConstIterator is an implementation of the {@link Iterator} interface for iterating over
   * a collection of {@code DatatypeSelector} objects.
   * It provides read-only access to the elements.
   */
  public class ConstIterator implements Iterator<DatatypeSelector>
  {
    private int currentIndex;
    private int size;

    /**
     * Constructs a new ConstIterator.
     */
    public ConstIterator()
    {
      currentIndex = -1;
      size = getNumSelectors();
    }

    @Override
    public boolean hasNext()
    {
      return currentIndex < size - 1;
    }

    @Override
    public DatatypeSelector next()
    {
      if (currentIndex >= size - 1)
      {
        throw new NoSuchElementException();
      }
      currentIndex++;

      return getSelector(currentIndex);
    }
  }

  @Override
  public Iterator<DatatypeSelector> iterator()
  {
    return new ConstIterator();
  }

  /**
   * Get the hash value of a datatype constructor.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(getPointer()));
  }

  private long hashCode(long pointer)
  {
    if (pointer == 0)
    {
      return 0;
    }
    return CApi.cvc5_dt_cons_hash(pointer);
  }
}
