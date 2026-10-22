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

import io.github.cvc5.capi.CApi;
import java.lang.foreign.MemorySegment;

/**
 * A cvc5 datatype selector.
 */
public class DatatypeSelector extends AbstractPointer
{
  // region construction and destruction
  DatatypeSelector(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, DatatypeSelector::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
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
    if (address() == sel.address())
    {
      return true;
    }
    return equals(handle(), sel.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_dt_sel_is_equal(pointer1, pointer2));
  }

  /**
   * Get the Name of this Datatype selector.
   *
   * @return The Name of this Datatype selector.
   */
  public String getName()
  {
    return getName(handle());
  }

  private String getName(MemorySegment pointer)
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
    MemorySegment termPointer = getTerm(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getTerm(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_dt_sel_get_term(pointer));
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
    MemorySegment termPointer = getUpdaterTerm(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getUpdaterTerm(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_dt_sel_get_updater_term(pointer));
  }

  /**
   * Get the Codomain sort of this selector.
   *
   * @return The Codomain sort of this selector.
   */
  public Sort getCodomainSort()
  {
    MemorySegment sortPointer = getCodomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getCodomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_dt_sel_get_codomain_sort(pointer));
  }

  /**
   * Determine if this DatatypeSelector is a null object.
   *
   * @return True If this DatatypeSelector is a null object.
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
   * @return A String representation of this datatype selector.
   */
  protected String toString(long pointer)
  {
    return Native.string(CApi.cvc5_dt_sel_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * Get the hash value of a datatype selector.
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
    return Native.check(CApi.cvc5_dt_sel_hash(pointer));
  }
}
