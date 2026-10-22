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

/**
 * A cvc5 datatype selector.
 */
public class DatatypeSelector extends AbstractPointer
{
  // region construction and destruction
  DatatypeSelector(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, DatatypeSelector::deletePointer);
  }

  private static void deletePointer(long pointer)
  {
    CApi.cvc5_dt_sel_release(pointer);
  }

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
    return equals(getPointer(), sel.getPointer());
  }

  private boolean equals(long pointer1, long pointer2)
  {
    return CApi.cvc5_dt_sel_is_equal(pointer1, pointer2);
  }

  /**
   * Get the Name of this Datatype selector.
   *
   * @return The Name of this Datatype selector.
   */
  public String getName()
  {
    return getName(getPointer());
  }

  private String getName(long pointer)
  {
    return Native.string(CApi.cvc5_dt_sel_get_name(pointer));
  }

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
    long termPointer = getTerm(getPointer());
    return new Term(ctx, termPointer);
  }

  private long getTerm(long pointer)
  {
    return CApi.cvc5_dt_sel_get_term(pointer);
  }

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
    long termPointer = getUpdaterTerm(getPointer());
    return new Term(ctx, termPointer);
  }

  private long getUpdaterTerm(long pointer)
  {
    return CApi.cvc5_dt_sel_get_updater_term(pointer);
  }

  /**
   * Get the Codomain sort of this selector.
   *
   * @return The Codomain sort of this selector.
   */
  public Sort getCodomainSort()
  {
    long sortPointer = getCodomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private long getCodomainSort(long pointer)
  {
    return CApi.cvc5_dt_sel_get_codomain_sort(pointer);
  }

  /**
   * Determine if this DatatypeSelector is a null object.
   *
   * @return True If this DatatypeSelector is a null object.
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
   * @return A String representation of this datatype selector.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_dt_sel_to_string(pointer));
  }

  /**
   * Get the hash value of a datatype selector.
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
    return CApi.cvc5_dt_sel_hash(pointer);
  }
}
