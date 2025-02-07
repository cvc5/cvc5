/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
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

import java.util.*;

public class SymbolManager extends AbstractPointer
{
  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package.
   * @param pointer The cpp pointer to symbol manager.
   */
  SymbolManager(long pointer)
  {
    super(pointer);
  }

  /**
   * Create symbol manager instance.
   * @param tm The associated term manager.
   */
  public SymbolManager(TermManager tm)
  {
    super(newSymbolManager(tm.getPointer()));
  }

  /**
   * Create symbol manager instance.
   * @param solver The associated solver.
   * @deprecated
   * This function is deprecated and replaced by
   * {@link Solver#Solver(TermManager)}.
   * It will be removed in a future release.
   */
  @Deprecated
  public SymbolManager(Solver solver)
  {
    this(solver.getTermManager());
  }

  private static native long newSymbolManager(long solverPointer);

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "SymbolManager.toString() is not supported in the cpp api");
  }
  protected native void deletePointer(long pointer);

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
    SymbolManager symbolManager = (SymbolManager) s;
    if (this.pointer == symbolManager.pointer)
    {
      return true;
    }
    return false;
  }

  /**
   * @return True if the logic of this symbol manager has been set.
   */
  public boolean isLogicSet()
  {
    return isLogicSet(pointer);
  }

  private native boolean isLogicSet(long pointer);

  /**
   * @api.note Asserts isLogicSet().
   *
   * @return The logic used by this symbol manager.
   */
  public String getLogic()
  {
    return getLogic(pointer);
  }

  private native String getLogic(long pointer);

  /**
   * Get the list of sorts that have been declared via `declare-sort` commands.
   * These are the sorts that are printed as part of a response to a
   * `get-model` command.
   *
   * @return The declared sorts.
   */
  public Sort[] getDeclaredSorts()
  {
    long[] pointers = getDeclaredSorts(pointer);
    return Utils.getSorts(pointers);
  }

  private native long[] getDeclaredSorts(long pointer);

  /**
   * Get the list of terms that have been declared via `declare-fun` and
   * `declare-const`. These are the terms that are printed in response to a
   * `get-model` command.
   *
   * @return The declared terms.
   */
  public Term[] getDeclaredTerms()
  {
    long[] retPointers = getDeclaredTerms(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getDeclaredTerms(long pointer);



  /**
   * Get a mapping from terms to names that have been given to them via the
   * :named attribute.
   *
   * @return A map of the named terms to their names.
   */
  public Map<Term, String> getNamedTerms()
  {
    Map<Long, String> map = getNamedTerms(pointer);
    Map<Term, String> ret = new HashMap<>();
    for (Map.Entry<Long, String> entry : map.entrySet())
    {
      Term key = new Term(entry.getKey());
      String value = entry.getValue();
      ret.put(key, value);
    }
    return ret;
  }

  private native Map<Long, String> getNamedTerms(long pointer);
}
