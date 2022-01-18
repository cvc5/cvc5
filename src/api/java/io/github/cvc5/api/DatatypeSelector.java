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

public class DatatypeSelector extends AbstractPointer
{
  // region construction and destruction
  DatatypeSelector(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /** @return the name of this Datatype selector. */
  public String getName()
  {
    return getName(pointer);
  }

  private native String getName(long pointer);

  /**
   * Get the selector operator of this datatype selector.
   * @return the selector term
   */
  public Term getSelectorTerm()
  {
    long termPointer = getSelectorTerm(pointer);
    return new Term(solver, termPointer);
  }

  private native long getSelectorTerm(long pointer);

  /**
   * Get the upater operator of this datatype selector.
   * @return the updater term
   */
  public Term getUpdaterTerm()
  {
    long termPointer = getUpdaterTerm(pointer);
    return new Term(solver, termPointer);
  }

  private native long getUpdaterTerm(long pointer);

  /** @return the codomain sort of this selector. */
  public Sort getCodomainSort()
  {
    long sortPointer = getCodomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getCodomainSort(long pointer);

  /**
   * @return true if this DatatypeSelector is a null object
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * @return a string representation of this datatype selector
   */
  protected native String toString(long pointer);
}
