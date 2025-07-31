/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
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

  // endregion

  /**
   * Syntactic equality operator.
   *
   * @param s The datatype selector to compare to for equality.
   * @return True if the datatype selectors are equal.
   */
  @Override
  public boolean equals(Object s)
  {
    if (this == s)
    {
      return true;
    }
    if (s == null || getClass() != s.getClass())
    {
      return false;
    }
    DatatypeSelector sel = (DatatypeSelector) s;
    if (this.pointer == sel.pointer)
    {
      return true;
    }
    return equals(pointer, sel.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Get the Name of this Datatype selector.
   *
   * @return The Name of this Datatype selector.
   */
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

  /**
   * Get the Codomain sort of this selector.
   *
   * @return The Codomain sort of this selector.
   */
  public Sort getCodomainSort()
  {
    long sortPointer = getCodomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getCodomainSort(long pointer);

  /**
   * Determine if this DatatypeSelector is a null object.
   *
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

  /**
   * Get the hash value of a datatype selector.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return hashCode(pointer);
  }

  private native int hashCode(long pointer);
}
