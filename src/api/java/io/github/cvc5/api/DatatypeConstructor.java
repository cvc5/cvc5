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

public class DatatypeConstructor extends AbstractPointer implements Iterable<DatatypeSelector>
{
  // region construction and destruction
  DatatypeConstructor(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /** @return the name of this Datatype constructor. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

  /**
   * Get the constructor operator of this datatype constructor.
   * @return the constructor term
   */
  public Term getConstructorTerm()
  {
    long termPointer = getConstructorTerm(pointer);
    return new Term(solver, termPointer);
  }

  private native long getConstructorTerm(long pointer);

  /**
   * Get the constructor operator of this datatype constructor whose return
   * type is retSort. This method is intended to be used on constructors of
   * parametric datatypes and can be seen as returning the constructor
   * term that has been explicitly cast to the given sort.
   *
   * This method is required for constructors of parametric datatypes whose
   * return type cannot be determined by type inference. For example, given:
   *   (declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))
   * The type of nil terms need to be provided by the user. In SMT version 2.6,
   * this is done via the syntax for qualified identifiers:
   *   (as nil (List Int))
   * This method is equivalent of applying the above, where this
   * DatatypeConstructor is the one corresponding to nil, and retSort is
   * (List Int).
   *
   * Furthermore note that the returned constructor term t is an operator,
   * while Solver::mkTerm(APPLY_CONSTRUCTOR, t) is used to construct the above
   * (nullary) application of nil.
   *
   * @param retSort the desired return sort of the constructor
   * @return the constructor term
   */
  public Term getInstantiatedConstructorTerm(Sort retSort) {
    long termPointer =
        getInstantiatedConstructorTerm(pointer, retSort.getPointer());
    return new Term(solver, termPointer);
  }

  private native long getInstantiatedConstructorTerm(
      long pointer, long retSortPointer);

  /**
   * Get the tester operator of this datatype constructor.
   * @return the tester operator
   */
  public Term getTesterTerm()
  {
    long termPointer = getTesterTerm(pointer);
    return new Term(solver, termPointer);
  }
  private native long getTesterTerm(long pointer);

  /**
   * @return the number of selectors (so far) of this Datatype constructor.
   */
  public int getNumSelectors()
  {
    return getNumSelectors(pointer);
  }
  private native int getNumSelectors(long pointer);

  /** @return the i^th DatatypeSelector. */
  public DatatypeSelector getSelector(int index)
  {
    long selectorPointer = getSelector(pointer, index);
    return new DatatypeSelector(solver, selectorPointer);
  }
  private native long getSelector(long pointer, int index);

  /**
   * Get the datatype selector with the given name.
   * This is a linear search through the selectors, so in case of
   * multiple, similarly-named selectors, the first is returned.
   * @param name the name of the datatype selector
   * @return the first datatype selector with the given name
   */
  public DatatypeSelector getSelector(String name)
  {
    long selectorPointer = getSelector(pointer, name);
    return new DatatypeSelector(solver, selectorPointer);
  }
  private native long getSelector(long pointer, String name);

  /**
   * Get the term representation of the datatype selector with the given name.
   * This is a linear search through the arguments, so in case of multiple,
   * similarly-named arguments, the selector for the first is returned.
   * @param name the name of the datatype selector
   * @return a term representing the datatype selector with the given name
   */
  public Term getSelectorTerm(String name)
  {
    long termPointer = getSelectorTerm(pointer, name);
    return new Term(solver, termPointer);
  }
  private native long getSelectorTerm(long pointer, String name);

  /**
   * @return true if this DatatypeConstructor is a null object
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return a string representation of this datatype constructor
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

    @Override public boolean hasNext()
    {
      return currentIndex < size - 1;
    }

    @Override public DatatypeSelector next()
    {
      if (currentIndex >= size - 1)
      {
        throw new NoSuchElementException();
      }
      currentIndex++;

      return getSelector(currentIndex);
    }
  }

  @Override public Iterator<DatatypeSelector> iterator()
  {
    return new ConstIterator();
  }
}
