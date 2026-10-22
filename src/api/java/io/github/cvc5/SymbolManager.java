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

import static java.lang.foreign.ValueLayout.ADDRESS;
import static java.lang.foreign.ValueLayout.JAVA_LONG;

import io.github.cvc5.capi.CApi;
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
    super(tm.ctx, newSymbolManager(tm.handle()), SymbolManager::deletePointer);
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

  private static MemorySegment newSymbolManager(MemorySegment solverPointer)
  {
    return Native.handle(CApi.cvc5_symbol_manager_new(solverPointer));
  }

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "SymbolManager.toString() is not supported in the cpp api");
  }
  private static void deletePointer(MemorySegment pointer)
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
    if (address() == symbolManager.address())
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
    return Long.hashCode(handle().address());
  }

  /**
   * Determine if the logic of this symbol manager has been set.
   *
   * @return True if the logic of this symbol manager has been set.
   */
  public boolean isLogicSet()
  {
    return isLogicSet(handle());
  }

  private boolean isLogicSet(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sm_is_logic_set(pointer));
  }

  /**
   * Get the logic used by this symbol manager.
   *
   * @api.note Asserts isLogicSet().
   * @return The logic used by this symbol manager.
   */
  public String getLogic()
  {
    return getLogic(handle());
  }

  private String getLogic(MemorySegment pointer)
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
    MemorySegment[] pointers = getDeclaredSorts(handle());
    return Utils.getSorts(ctx, pointers);
  }

  private MemorySegment[] getDeclaredSorts(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment sorts = Native.check(CApi.cvc5_sm_get_declared_sorts(pointer, size));
      return Native.handles(sorts, size.get(JAVA_LONG, 0));
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
    MemorySegment[] retPointers = getDeclaredTerms(handle());
    return Utils.getTerms(ctx, retPointers);
  }

  private MemorySegment[] getDeclaredTerms(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment terms = Native.check(CApi.cvc5_sm_get_declared_terms(pointer, size));
      return Native.handles(terms, size.get(JAVA_LONG, 0));
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
    Map<MemorySegment, String> map = getNamedTerms(handle());
    Map<Term, String> ret = new HashMap<>();
    for (Map.Entry<MemorySegment, String> entry : map.entrySet())
    {
      Term key = new Term(ctx, entry.getKey());
      String value = entry.getValue();
      ret.put(key, value);
    }
    return ret;
  }

  private Map<MemorySegment, String> getNamedTerms(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment terms = arena.allocate(ADDRESS);
      MemorySegment names = arena.allocate(ADDRESS);
      CApi.cvc5_sm_get_named_terms(pointer, size, terms, names);
      Native.check();
      long n = size.get(JAVA_LONG, 0);
      MemorySegment[] termPointers = Native.handles(terms.get(ADDRESS, 0), n);
      String[] termNames = Native.strings(names.get(ADDRESS, 0), n);
      Map<MemorySegment, String> map = new HashMap<>();
      for (int i = 0; i < termPointers.length; i++)
      {
        map.put(termPointers[i], termNames[i]);
      }
      return map;
    }
  }
}
