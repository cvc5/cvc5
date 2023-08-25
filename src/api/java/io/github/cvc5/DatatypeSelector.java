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

/**
 * A cvc5 datatype selector.
 */
public class DatatypeSelector extends AbstractPointer
{
  // region construction and destruction
  DatatypeSelector(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /** @return The Name of this Datatype selector. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

  /**
   * Get the selector term of this datatype selector.
   *
   * Selector terms are a class of function-like terms of selector
   * sort (Sort::isDatatypeSelector), and should be used as the first
   * argument of Terms of kind APPLY_SELECTOR.
   *
   * @return The Selector term.
   */
  public Term getTerm()
  {
    long termPointer = getTerm(pointer);
    return new Term(termPointer);
  }

  private native long getTerm(long pointer);

  /**
   * Get the updater term of this datatype selector.
   *
   * Similar to selectors, updater terms are a class of function-like terms of
   * updater Sort (Sort::isDatatypeUpdater), and should be used as the first
   * argument of Terms of kind APPLY_UPDATER.
   *
   * @return The Updater term.
   */
  public Term getUpdaterTerm()
  {
    long termPointer = getUpdaterTerm(pointer);
    return new Term(termPointer);
  }

  private native long getUpdaterTerm(long pointer);

  /** @return The Codomain sort of this selector. */
  public Sort getCodomainSort()
  {
    long sortPointer = getCodomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getCodomainSort(long pointer);

  /**
   * @return True If this DatatypeSelector is a null object.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return A String representation of this datatype selector.
   */
  protected native String toString(long pointer);
}
