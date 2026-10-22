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

import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.util.*;

/**
 * Symbol manager. Internally, this class manages a symbol table and other
 * meta-information pertaining to SMT2 file inputs (e.g. named assertions,
 * declared functions, etc.).
 *
 * A symbol manager can be modified by invoking commands, see
 * {@link Command#invoke(Solver, SymbolManager)}.
 *
 * A symbol manager can be provided when constructing an InputParser, in which
 * case that InputParser has symbols of this symbol manager preloaded.
 *
 * The symbol manager's interface is otherwise not publicly available.
 */
public class SymbolManager extends AbstractPointer implements AutoCloseable
{
  /**
   * Create symbol manager instance.
   * @param tm The associated term manager.
   */
  public SymbolManager(TermManager tm)
  {
    super(tm.ctx, newSymbolManager(tm.getPointer()), SymbolManager::deletePointer);
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

  private static long newSymbolManager(long solverPointer)
  {
    return CApi.cvc5_symbol_manager_new(solverPointer);
  }

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "SymbolManager.toString() is not supported in the cpp api");
  }
  private static void deletePointer(long pointer)
  {
    CApi.cvc5_symbol_manager_delete(pointer);
  }

  /**
   * Free the native symbol manager, see {@code deletePointer()}.
   */
  @Override
  public void close()
  {
    deletePointer();
  }

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
   * Return a hash code value for this symbol manager.
   *
   * The hash code is derived from the underlying native pointer, which is what
   * {@link #equals(Object)} compares, so that instances that are equal have the
   * same hash code.
   *
   * @return a hash code value for this symbol manager
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(getPointer());
  }

  /**
   * Determine if the logic of this symbol manager has been set.
   *
   * @return True if the logic of this symbol manager has been set.
   */
  public boolean isLogicSet()
  {
    return isLogicSet(getPointer());
  }

  private boolean isLogicSet(long pointer)
  {
    return CApi.cvc5_sm_is_logic_set(pointer);
  }

  /**
   * Get the logic used by this symbol manager.
   *
   * @api.note Asserts isLogicSet().
   * @return The logic used by this symbol manager.
   */
  public String getLogic()
  {
    return getLogic(getPointer());
  }

  private String getLogic(long pointer)
  {
    return Native.string(CApi.cvc5_sm_get_logic(pointer));
  }

  /**
   * Get the list of sorts that have been declared via `declare-sort` commands.
   * These are the sorts that are printed as part of a response to a
   * `get-model` command.
   *
   * @return The declared sorts.
   */
  public Sort[] getDeclaredSorts()
  {
    long[] pointers = getDeclaredSorts(getPointer());
    return Utils.getSorts(ctx, pointers);
  }

  private long[] getDeclaredSorts(long pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = Native.outLong(arena);
      long sorts = CApi.cvc5_sm_get_declared_sorts(pointer, size.address());
      return Native.longs(sorts, size.get(JAVA_LONG, 0));
    }
  }

  /**
   * Get the list of terms that have been declared via `declare-fun` and
   * `declare-const`. These are the terms that are printed in response to a
   * `get-model` command.
   *
   * @return The declared terms.
   */
  public Term[] getDeclaredTerms()
  {
    long[] retPointers = getDeclaredTerms(getPointer());
    return Utils.getTerms(ctx, retPointers);
  }

  private long[] getDeclaredTerms(long pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = Native.outLong(arena);
      long terms = CApi.cvc5_sm_get_declared_terms(pointer, size.address());
      return Native.longs(terms, size.get(JAVA_LONG, 0));
    }
  }

  /**
   * Get a mapping from terms to names that have been given to them via the
   * :named attribute.
   *
   * @return A map of the named terms to their names.
   */
  public Map<Term, String> getNamedTerms()
  {
    Map<Long, String> map = getNamedTerms(getPointer());
    Map<Term, String> ret = new HashMap<>();
    for (Map.Entry<Long, String> entry : map.entrySet())
    {
      Term key = new Term(ctx, entry.getKey());
      String value = entry.getValue();
      ret.put(key, value);
    }
    return ret;
  }

  private Map<Long, String> getNamedTerms(long pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = Native.outLong(arena);
      MemorySegment terms = Native.outLong(arena);
      MemorySegment names = Native.outLong(arena);
      CApi.cvc5_sm_get_named_terms(pointer, size.address(), terms.address(), names.address());
      long n = size.get(JAVA_LONG, 0);
      long[] termPointers = Native.longs(terms.get(JAVA_LONG, 0), n);
      String[] termNames = Native.strings(names.get(JAVA_LONG, 0), n);
      Map<Long, String> map = new HashMap<>();
      for (int i = 0; i < termPointers.length; i++)
      {
        map.put(termPointers[i], termNames[i]);
      }
      return map;
    }
  }
}
