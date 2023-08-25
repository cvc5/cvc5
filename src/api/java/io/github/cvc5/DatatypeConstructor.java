/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
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
 * A cvc5 datatype constructor.
 */
public class DatatypeConstructor extends AbstractPointer implements Iterable<DatatypeSelector>
{
  // region construction and destruction
  DatatypeConstructor(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /** @return The name of this Datatype constructor. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

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
    long termPointer = getTerm(pointer);
    return new Term(termPointer);
  }

  private native long getTerm(long pointer);

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
    long termPointer = getInstantiatedTerm(pointer, retSort.getPointer());
    return new Term(termPointer);
  }

  private native long getInstantiatedTerm(long pointer, long retSortPointer);

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
    long termPointer = getTesterTerm(pointer);
    return new Term(termPointer);
  }
  private native long getTesterTerm(long pointer);

  /**
   * @return The number of selectors (so far) of this Datatype constructor.
   */
  public int getNumSelectors()
  {
    return getNumSelectors(pointer);
  }
  private native int getNumSelectors(long pointer);

  /**
   * Get the DatatypeSelector at the given index
   * @param index The given index i.
   * @return The i^th DatatypeSelector.
   */
  public DatatypeSelector getSelector(int index)
  {
    long selectorPointer = getSelector(pointer, index);
    return new DatatypeSelector(selectorPointer);
  }
  private native long getSelector(long pointer, int index);

  /**
   * Get the datatype selector with the given name.
   * This is a linear search through the selectors, so in case of
   * multiple, similarly-named selectors, the first is returned.
   * @param name The name of the datatype selector.
   * @return The first datatype selector with the given name.
   */
  public DatatypeSelector getSelector(String name)
  {
    long selectorPointer = getSelector(pointer, name);
    return new DatatypeSelector(selectorPointer);
  }
  private native long getSelector(long pointer, String name);

  /**
   * @return True if this DatatypeConstructor is a null object.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return A string representation of this datatype constructor.
   */
  protected native String toString(long pointer);

  public class ConstIterator implements Iterator<DatatypeSelector>
  {
    private int currentIndex;
    private int size;

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
}
