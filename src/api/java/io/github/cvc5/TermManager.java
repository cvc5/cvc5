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
import java.io.IOException;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.util.*;

/**
 * A cvc5 term manager.
 */
public class TermManager extends AbstractPointer implements AutoCloseable
{
  static
  {
    Utils.loadLibraries();
  }

  private static MemorySegment newTermManager()
  {
    return Native.handle(CApi.cvc5_term_manager_new());
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_term_manager_delete(pointer);
  }

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException(
        "TermManager.toString() is not supported in the cpp api");
  }

  /**
   * Create a term manager instance.
   */
  public TermManager()
  {
    this(TermManager.newTermManager());
  }

  private TermManager(MemorySegment pointer)
  {
    super(new NativeContext(pointer), pointer, TermManager::deletePointer);
  }

  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package. It wraps the term manager of a context without
   * owning a reference to it; the context keeps it alive.
   * @param ctx The context of the term manager.
   */
  TermManager(NativeContext ctx)
  {
    super(ctx, ctx.tm, null);
  }

  /**
   * Free the native term manager, see {@code deletePointer()}.
   *
   * <p>Objects created via this term manager remain valid, they keep the
   * underlying node manager alive.</p>
   */
  @Override
  public void close()
  {
    deletePointer();
  }

  @Override
  public boolean equals(Object o)
  {
    if (this == o)
    {
      return true;
    }
    if (o == null || getClass() != o.getClass())
    {
      return false;
    }
    // Term managers are equal if they share the same node manager, e.g., a
    // term manager and the copy returned by Solver.getTermManager(). Exactly
    // those share a context.
    return ctx == ((TermManager) o).ctx;
  }

  /**
   * Return a hash code value for this term manager.
   *
   * The hash code is derived from the context of the underlying node manager,
   * which is what {@link #equals(Object)} compares, so that instances that are
   * equal have the same hash code.
   *
   * @return a hash code value for this term manager
   */
  @Override
  public int hashCode()
  {
    return System.identityHashCode(ctx);
  }

  /**
   * Get a snapshot of the current state of the statistic values of this
   * term manager.
   *
   * Term manager statistics are independent from any solver instance. The
   * returned object is completely decoupled from the term manager and will
   * not change when the solver is used again.
   *
   * @return A snapshot of the current state of the statistic values.
   */
  public Statistics getStatistics()
  {
    MemorySegment statisticsPointer = getStatistics(handle());
    return new Statistics(ctx, statisticsPointer);
  }

  private MemorySegment getStatistics(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_term_manager_get_statistics(pointer));
  }

  /* .................................................................... */
  /* Sorts Handling                                                       */
  /* .................................................................... */

  /**
   * Get the Boolean sort.
   * @return Sort Boolean.
   */
  public Sort getBooleanSort()
  {
    MemorySegment sortPointer = getBooleanSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getBooleanSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_get_boolean_sort(pointer));
  }

  /**
   * Get the integer sort.
   * @return Sort Integer.
   */
  public Sort getIntegerSort()
  {
    MemorySegment sortPointer = getIntegerSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getIntegerSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_get_integer_sort(pointer));
  }
  /**
   * Get the real sort.
   * @return Sort Real.
   */
  public Sort getRealSort()
  {
    MemorySegment sortPointer = getRealSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getRealSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_get_real_sort(pointer));
  }
  /**
   * Get the regular expression sort.
   * @return Sort RegExp.
   */
  public Sort getRegExpSort()
  {
    MemorySegment sortPointer = getRegExpSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getRegExpSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_get_regexp_sort(pointer));
  }
  /**
   * Get the floating-point rounding mode sort.
   * @return Sort RoundingMode.
   * @throws CVC5ApiException on error
   */
  public Sort getRoundingModeSort() throws CVC5ApiException
  {
    MemorySegment sortPointer = getRoundingModeSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getRoundingModeSort(MemorySegment pointer) throws CVC5ApiException
  {
    return Native.handle(CApi.cvc5_get_rm_sort(pointer));
  }

  /**
   * Get the string sort.
   * @return Sort String.
   */
  public Sort getStringSort()
  {
    MemorySegment sortPointer = getStringSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getStringSort(MemorySegment solverPointer)
  {
    return Native.handle(CApi.cvc5_get_string_sort(solverPointer));
  }
  /**
   * Create an array sort.
   * @param indexSort The array index sort.
   * @param elemSort The array element sort.
   * @return The array sort.
   */
  public Sort mkArraySort(Sort indexSort, Sort elemSort)
  {
    MemorySegment sortPointer = mkArraySort(handle(), indexSort.handle(), elemSort.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkArraySort(
      MemorySegment pointer, MemorySegment indexSortPointer, MemorySegment elementSortPointer)
  {
    return Native.handle(CApi.cvc5_mk_array_sort(pointer, indexSortPointer, elementSortPointer));
  }

  /**
   * Create a bit-vector sort.
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkBitVectorSort(int size) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    MemorySegment sortPointer = mkBitVectorSort(handle(), size);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkBitVectorSort(MemorySegment pointer, int size)
  {
    return Native.handle(CApi.cvc5_mk_bv_sort(pointer, size));
  }

  /**
   * Create a finite field sort.
   * @param size The size of the finite field sort.
   * @param base The base of the string representation.
   * @return The finite field sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkFiniteFieldSort(String size, int base) throws CVC5ApiException
  {
    MemorySegment sortPointer = mkFiniteFieldSort(handle(), size, base);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkFiniteFieldSort(MemorySegment pointer, String size, int base)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_ff_sort(pointer, arena.allocateFrom(size), base));
    }
  }

  /**
   * Create a floating-point sort.
   * @param exp The bit-width of the exponent of the floating-point sort.
   * @param sig The bit-width of the significand of the floating-point sort.
   * @return The floating-point sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkFloatingPointSort(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment sortPointer = mkFloatingPointSort(handle(), exp, sig);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkFloatingPointSort(MemorySegment solverPointer, int exp, int sig)
  {
    return Native.handle(CApi.cvc5_mk_fp_sort(solverPointer, exp, sig));
  }

  /**
   * Create a datatype sort.
   * @param dtypedecl The datatype declaration from which the sort is created.
   * @return The datatype sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkDatatypeSort(DatatypeDecl dtypedecl) throws CVC5ApiException
  {
    MemorySegment pointer = mkDatatypeSort(handle(), dtypedecl.handle());
    return new Sort(ctx, pointer);
  }

  private MemorySegment mkDatatypeSort(MemorySegment pointer, MemorySegment datatypeDeclPointer)
      throws CVC5ApiException
  {
    return Native.handle(CApi.cvc5_mk_dt_sort(pointer, datatypeDeclPointer));
  }

  /**
   * Create a vector of datatype sorts.
   *
   * The names of the datatype declarations must be distinct.
   *
   * @param dtypedecls The datatype declarations from which the sort is created.
   * @return The datatype sorts.
   * @throws CVC5ApiException on error
   */
  public Sort[] mkDatatypeSorts(DatatypeDecl[] dtypedecls) throws CVC5ApiException
  {
    MemorySegment[] declPointers = Utils.getHandles(dtypedecls);
    MemorySegment[] sortPointers = mkDatatypeSorts(handle(), declPointers);
    Sort[] sorts = Utils.getSorts(ctx, sortPointers);
    return sorts;
  }

  private MemorySegment[] mkDatatypeSorts(MemorySegment pointer, MemorySegment[] declPointers)
      throws CVC5ApiException
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment sorts = Native.check(CApi.cvc5_mk_dt_sorts(
          pointer, declPointers.length, Native.allocateHandles(arena, declPointers)));
      // one sort per datatype declaration
      return Native.handles(sorts, declPointers.length);
    }
  }

  /**
   * Create function sort.
   * @param domain The sort of the fuction argument.
   * @param codomain The sort of the function return value.
   * @return The function sort.
   */
  public Sort mkFunctionSort(Sort domain, Sort codomain)
  {
    return mkFunctionSort(new Sort[] {domain}, codomain);
  }

  /**
   * Create function sort.
   * @param sorts The sort of the function arguments.
   * @param codomain The sort of the function return value.
   * @return The function sort.
   */
  public Sort mkFunctionSort(Sort[] sorts, Sort codomain)
  {
    MemorySegment sortPointer =
        mkFunctionSort(handle(), Utils.getHandles(sorts), codomain.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkFunctionSort(
      MemorySegment pointer, MemorySegment[] sortPointers, MemorySegment codomainPointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_fun_sort(pointer,
          sortPointers.length,
          Native.allocateHandles(arena, sortPointers),
          codomainPointer));
    }
  }

  /**
   * Create a sort parameter.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param symbol The name of the sort.
   * @return The sort parameter.
   */
  public Sort mkParamSort(String symbol)
  {
    MemorySegment sortPointer = mkParamSort(handle(), symbol);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkParamSort(MemorySegment pointer, String symbol)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_param_sort(pointer, arena.allocateFrom(symbol)));
    }
  }

  /**
   * Create a sort parameter.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The sort parameter.
   */
  public Sort mkParamSort()
  {
    MemorySegment sortPointer = mkParamSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkParamSort(MemorySegment pointer)
  {
    // cvc5_mk_param_sort() requires a symbol. Without a symbol, the C++ API
    // creates a parameter sort exactly like an uninterpreted sort without a
    // symbol (NodeManager::mkSort()), which is what this C function does.
    return Native.handle(CApi.cvc5_mk_uninterpreted_sort(pointer, MemorySegment.NULL));
  }

  /**
   * Create a skolem
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param skolemId The id of the skolem.
   * @param indices The indices of the skolem.
   * @return The skolem.
   */
  public Term mkSkolem(SkolemId skolemId, Term[] indices)
  {
    MemorySegment skolemPointer =
        mkSkolem(handle(), skolemId.getValue(), Utils.getHandles(indices));
    return new Term(ctx, skolemPointer);
  }

  private MemorySegment mkSkolem(MemorySegment pointer, int skolemId, MemorySegment[] indices)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_skolem(
          pointer, skolemId, indices.length, Native.allocateHandles(arena, indices)));
    }
  }

  /**
   * Get the number of indices for a given skolem id.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param id The skolem id.
   * @return The number of indices for the given skolem id.
   */

  public int getNumIndicesForSkolemId(SkolemId id)
  {
    int numIndices = getNumIndicesForSkolemId(handle(), id.getValue());
    return numIndices;
  }

  private int getNumIndicesForSkolemId(MemorySegment pointer, int skolemId)
  {
    return (int) Native.check(CApi.cvc5_get_num_idxs_for_skolem_id(pointer, skolemId));
  }

  /**
   * Create a predicate sort.
   * @param sorts The list of sorts of the predicate.
   * @return The predicate sort.
   */
  public Sort mkPredicateSort(Sort[] sorts)
  {
    MemorySegment sortPointer = mkPredicateSort(handle(), Utils.getHandles(sorts));
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkPredicateSort(MemorySegment pointer, MemorySegment[] sortPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_predicate_sort(
          pointer, sortPointers.length, Native.allocateHandles(arena, sortPointers)));
    }
  }

  /**
   * Create a record sort
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param fields The list of fields of the record.
   * @return The record sort.
   */
  public Sort mkRecordSort(Pair<String, Sort>[] fields)
  {
    MemorySegment sortPointer = mkRecordSort(handle(), Utils.getHandlePairs(fields));
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkRecordSort(MemorySegment pointer, Pair<String, MemorySegment>[] fields)
  {
    String[] names = new String[fields.length];
    MemorySegment[] sortPointers = new MemorySegment[fields.length];
    for (int i = 0; i < fields.length; i++)
    {
      names[i] = fields[i].first;
      sortPointers[i] = fields[i].second;
    }
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_record_sort(pointer,
          fields.length,
          Native.allocateStrings(arena, names),
          Native.allocateHandles(arena, sortPointers)));
    }
  }

  /**
   * Create a set sort.
   * @param elemSort The sort of the set elements.
   * @return The set sort.
   */
  public Sort mkSetSort(Sort elemSort)
  {
    MemorySegment sortPointer = mkSetSort(handle(), elemSort.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkSetSort(MemorySegment pointer, MemorySegment elemSortPointer)
  {
    return Native.handle(CApi.cvc5_mk_set_sort(pointer, elemSortPointer));
  }
  /**
   * Create a bag sort.
   * @param elemSort The sort of the bag elements.
   * @return The bag sort.
   */
  public Sort mkBagSort(Sort elemSort)
  {
    MemorySegment sortPointer = mkBagSort(handle(), elemSort.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkBagSort(MemorySegment pointer, MemorySegment elemSortPointer)
  {
    return Native.handle(CApi.cvc5_mk_bag_sort(pointer, elemSortPointer));
  }

  /**
   * Create a sequence sort.
   * @param elemSort The sort of the sequence elements.
   * @return The sequence sort.
   */
  public Sort mkSequenceSort(Sort elemSort)
  {
    MemorySegment sortPointer = mkSequenceSort(handle(), elemSort.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkSequenceSort(MemorySegment pointer, MemorySegment elemSortPointer)
  {
    return Native.handle(CApi.cvc5_mk_sequence_sort(pointer, elemSortPointer));
  }

  /**
   * Create an abstract sort. An abstract sort represents a sort for a given
   * kind whose parameters and arguments are unspecified.
   *
   * The {@link SortKind} k must be the kind of a sort that can be abstracted,
   * i.e., a sort that has indices or argument sorts. For example,
   * {@link SortKind#ARRAY_SORT} and {@link SortKind#BITVECTOR_SORT} can be
   * passed as the {@link SortKind} k to this method, while
   * {@link SortKind#INTEGER_SORT} and  {@link SortKind#STRING_SORT} cannot.
   *
   * @api.note Providing the kind  {@link SortKind#ABSTRACT_SORT} as an
   *           argument to this method returns the (fully) unspecified sort,
   *           often denoted {@code ?}.
   *
   * @api.note Providing a kind {@code k} that has no indices and a fixed arity
   *           of argument sorts will return the sort of {@link SortKind} k
   *           whose arguments are the unspecified sort. For example,
   *           {@code mkAbstractSort(ARRAY_SORT)} will return the sort
   *           {@code (ARRAY_SORT ? ?)} instead of the abstract sort whose
   *           abstract kind is {@link SortKind#ABSTRACT_SORT}.
   *
   * @param kind The kind of the abstract sort
   * @return The abstract sort.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Sort mkAbstractSort(SortKind kind)
  {
    MemorySegment sortPointer = mkAbstractSort(handle(), kind.getValue());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkAbstractSort(MemorySegment pointer, int kindValue)
  {
    return Native.handle(CApi.cvc5_mk_abstract_sort(pointer, kindValue));
  }

  /**
   * Create an uninterpreted sort.
   * @param symbol The name of the sort.
   * @return The uninterpreted sort.
   */
  public Sort mkUninterpretedSort(String symbol)
  {
    MemorySegment sortPointer = mkUninterpretedSort(handle(), symbol);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkUninterpretedSort(MemorySegment pointer, String symbol)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_uninterpreted_sort(pointer, arena.allocateFrom(symbol)));
    }
  }

  /**
   * Create an uninterpreted sort.
   * @return The uninterpreted sort.
   */
  public Sort mkUninterpretedSort()
  {
    MemorySegment sortPointer = mkUninterpretedSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkUninterpretedSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_uninterpreted_sort(pointer, MemorySegment.NULL));
  }

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive parametric datatypes.
   *
   * @param symbol The symbol of the sort.
   * @param arity The number of sort parameters of the sort.
   * @return The unresolved sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkUnresolvedDatatypeSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    MemorySegment sortPointer = mkUnresolvedDatatypeSort(handle(), symbol, arity);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkUnresolvedDatatypeSort(MemorySegment pointer, String symbol, int arity)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(
          CApi.cvc5_mk_unresolved_dt_sort(pointer, arena.allocateFrom(symbol), arity));
    }
  }

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive datatypes without sort parameters.
   *
   * @param symbol The symbol of the sort.
   * @return The unresolved sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkUnresolvedDatatypeSort(String symbol) throws CVC5ApiException
  {
    return mkUnresolvedDatatypeSort(symbol, 0);
  }

  /**
   * Create a sort constructor sort.
   *
   * An uninterpreted sort constructor is an uninterpreted sort with
   * arity &gt; 0.
   *
   * @param arity The arity of the sort (must be &gt; 0)
   * @param symbol The symbol of the sort.
   * @return The sort constructor sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkUninterpretedSortConstructorSort(int arity, String symbol) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    MemorySegment sortPointer = mkUninterpretedSortConstructorSort(handle(), arity, symbol);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkUninterpretedSortConstructorSort(
      MemorySegment pointer, int arity, String symbol)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_uninterpreted_sort_constructor_sort(
          pointer, arity, arena.allocateFrom(symbol)));
    }
  }

  /**
   * Create a sort constructor sort.
   *
   * An uninterpreted sort constructor is an uninterpreted sort with
   * arity &gt; 0.
   *
   * @param arity The arity of the sort (must be &gt; 0)
   * @return The sort constructor sort.
   * @throws CVC5ApiException on error
   */
  public Sort mkUninterpretedSortConstructorSort(int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    MemorySegment sortPointer = mkUninterpretedSortConstructorSort(handle(), arity);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkUninterpretedSortConstructorSort(MemorySegment pointer, int arity)
  {
    return Native.handle(
        CApi.cvc5_mk_uninterpreted_sort_constructor_sort(pointer, arity, MemorySegment.NULL));
  }

  /**
   * Create a tuple sort.
   * @param sorts Of the elements of the tuple.
   * @return The tuple sort.
   */
  public Sort mkTupleSort(Sort[] sorts)
  {
    MemorySegment[] sortPointers = Utils.getHandles(sorts);
    MemorySegment sortPointer = mkTupleSort(handle(), sortPointers);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkTupleSort(MemorySegment pointer, MemorySegment[] sortPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_tuple_sort(
          pointer, sortPointers.length, Native.allocateHandles(arena, sortPointers)));
    }
  }

  /**
   * Create a nullable sort.
   *
   * @param sort The sort of the element of the nullable.
   * @return The nullable sort.
   */
  public Sort mkNullableSort(Sort sort)
  {
    MemorySegment sortPointer = mkNullableSort(handle(), sort.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment mkNullableSort(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_nullable_sort(pointer, sortPointer));
  }

  /* .................................................................... */
  /* Create Terms */
  /* .................................................................... */

  /**
   * Create 0-ary term of given kind.
   * @param kind The kind of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind)
  {
    MemorySegment termPointer = mkTerm(handle(), kind.getValue());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer, int kindValue)
  {
    return Native.handle(CApi.cvc5_mk_term(pointer, kindValue, 0, MemorySegment.NULL));
  }

  /**
   * Create a unary term of given kind.
   * @param kind The kind of the term.
   * @param child The child of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term child)
  {
    MemorySegment termPointer = mkTerm(handle(), kind.getValue(), child.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer, int kindValue, MemorySegment childPointer)
  {
    return mkTerm(pointer, kindValue, new MemorySegment[] {childPointer});
  }

  /**
   * Create binary term of given kind.
   * @param kind The kind of the term.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term child1, Term child2)
  {
    MemorySegment termPointer = mkTerm(handle(), kind.getValue(), child1.handle(), child2.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer,
      int kindValue,
      MemorySegment child1Pointer,
      MemorySegment child2Pointer)
  {
    return mkTerm(pointer, kindValue, new MemorySegment[] {child1Pointer, child2Pointer});
  }

  /**
   * Create ternary term of given kind.
   * @param kind The kind of the term.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @param child3 The third child of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term child1, Term child2, Term child3)
  {
    MemorySegment termPointer =
        mkTerm(handle(), kind.getValue(), child1.handle(), child2.handle(), child3.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer,
      int kindValue,
      MemorySegment child1Pointer,
      MemorySegment child2Pointer,
      MemorySegment child3Pointer)
  {
    return mkTerm(
        pointer, kindValue, new MemorySegment[] {child1Pointer, child2Pointer, child3Pointer});
  }
  /**
   * Create n-ary term of given kind.
   * @param kind The kind of the term.
   * @param children The children of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term[] children)
  {
    MemorySegment[] childPointers = Utils.getHandles(children);
    MemorySegment termPointer = mkTerm(handle(), kind.getValue(), childPointers);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(
      MemorySegment pointer, int kindValue, MemorySegment[] childrenPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_term(pointer,
          kindValue,
          childrenPointers.length,
          Native.allocateHandles(arena, childrenPointers)));
    }
  }

  /**
   * Create nullary term of given kind from a given operator.
   * Create operators with {@link TermManager#mkOp(Kind)},
   * {@link TermManager#mkOp(Kind, String)}, {@link TermManager#mkOp(Kind, int[])}.
   * @param op The operator.
   * @return The Term.
   */
  public Term mkTerm(Op op)
  {
    MemorySegment termPointer = mkTerm(handle(), op.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer, MemorySegment opPointer)
  {
    return Native.handle(CApi.cvc5_mk_term_from_op(pointer, opPointer, 0, MemorySegment.NULL));
  }
  /**
   * Create unary term of given kind from a given operator.
   * Create operators with {@link TermManager#mkOp(Kind)},
   * {@link TermManager#mkOp(Kind, String)}, {@link TermManager#mkOp(Kind, int[])}.
   * @param op The operator.
   * @param child The child of the term.
   * @return The Term.
   */
  public Term mkTerm(Op op, Term child)
  {
    MemorySegment termPointer = mkTerm(handle(), op.handle(), child.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(
      MemorySegment pointer, MemorySegment opPointer, MemorySegment childPointer)
  {
    return mkTerm(pointer, opPointer, new MemorySegment[] {childPointer});
  }

  /**
   * Create binary term of given kind from a given operator.
   * Create operators with {@link TermManager#mkOp(Kind)},
   * {@link TermManager#mkOp(Kind, String)}, {@link TermManager#mkOp(Kind, int[])}.
   * @param op The operator.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @return The Term.
   */
  public Term mkTerm(Op op, Term child1, Term child2)
  {
    MemorySegment termPointer = mkTerm(handle(), op.handle(), child1.handle(), child2.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer,
      MemorySegment opPointer,
      MemorySegment child1Pointer,
      MemorySegment child2Pointer)
  {
    return mkTerm(pointer, opPointer, new MemorySegment[] {child1Pointer, child2Pointer});
  }
  /**
   * Create ternary term of given kind from a given operator.
   * Create operators with {@link TermManager#mkOp(Kind)},
   * {@link TermManager#mkOp(Kind, String)}, {@link TermManager#mkOp(Kind, int[])}.
   * @param op The operator.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @param child3 The third child of the term.
   * @return The Term.
   */
  public Term mkTerm(Op op, Term child1, Term child2, Term child3)
  {
    MemorySegment termPointer =
        mkTerm(handle(), op.handle(), child1.handle(), child2.handle(), child3.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(MemorySegment pointer,
      MemorySegment opPointer,
      MemorySegment child1Pointer,
      MemorySegment child2Pointer,
      MemorySegment child3Pointer)
  {
    return mkTerm(
        pointer, opPointer, new MemorySegment[] {child1Pointer, child2Pointer, child3Pointer});
  }

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with {@link TermManager#mkOp(Kind)},
   * {@link TermManager#mkOp(Kind, String)}, {@link TermManager#mkOp(Kind, int[])}.
   * @param op The operator.
   * @param children The children of the term.
   * @return The Term.
   */
  public Term mkTerm(Op op, Term[] children)
  {
    MemorySegment[] childPointers = Utils.getHandles(children);
    MemorySegment termPointer = mkTerm(handle(), op.handle(), childPointers);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTerm(
      MemorySegment pointer, MemorySegment opPointer, MemorySegment[] childrenPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_term_from_op(pointer,
          opPointer,
          childrenPointers.length,
          Native.allocateHandles(arena, childrenPointers)));
    }
  }

  /**
   * Create a tuple term.
   * Terms are automatically converted if sorts are compatible.
   * @param terms The elements in the tuple.
   * @return The tuple Term.
   */
  public Term mkTuple(Term[] terms)
  {
    MemorySegment[] termPointers = Utils.getHandles(terms);
    MemorySegment termPointer = mkTuple(handle(), termPointers);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTuple(MemorySegment pointer, MemorySegment[] termPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_tuple(
          pointer, termPointers.length, Native.allocateHandles(arena, termPointers)));
    }
  }

  /**
   * Create a nullable some term.
   * @param term The element value.
   * @return the Element value wrapped in some constructor.
   */
  public Term mkNullableSome(Term term)
  {
    MemorySegment termPointer = mkNullableSome(handle(), term.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkNullableSome(MemorySegment pointer, MemorySegment termPointer)
  {
    return Native.handle(CApi.cvc5_mk_nullable_some(pointer, termPointer));
  }

  /**
   * Create a selector for nullable term.
   * @param term A nullable term.
   * @return The element value of the nullable term.
   */
  public Term mkNullableVal(Term term)
  {
    MemorySegment termPointer = mkNullableVal(handle(), term.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkNullableVal(MemorySegment pointer, MemorySegment termPointer)
  {
    return Native.handle(CApi.cvc5_mk_nullable_val(pointer, termPointer));
  }

  /**
   * Create a null tester for a nullable term.
   * @param term A nullable term.
   * @return A tester whether term is null.
   */
  public Term mkNullableIsNull(Term term)
  {
    MemorySegment termPointer = mkNullableIsNull(handle(), term.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkNullableIsNull(MemorySegment pointer, MemorySegment termPointer)
  {
    return Native.handle(CApi.cvc5_mk_nullable_is_null(pointer, termPointer));
  }

  /**
   * Create a some tester for a nullable term.
   * @param term A nullable term.
   * @return A tester whether term is some.
   */
  public Term mkNullableIsSome(Term term)
  {
    MemorySegment termPointer = mkNullableIsSome(handle(), term.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkNullableIsSome(MemorySegment pointer, MemorySegment termPointer)
  {
    return Native.handle(CApi.cvc5_mk_nullable_is_some(pointer, termPointer));
  }

  /**
   * Create a constant representing a null value of the given sort.
   * @param sort The sort of the Nullable element.
   * @return The null constant.
   */
  public Term mkNullableNull(Sort sort)
  {
    MemorySegment termPointer = mkNullableNull(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkNullableNull(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_nullable_null(pointer, sortPointer));
  }
  /**
   * Create a term that lifts kind to nullable terms.
   * Example:
   * If we have the term ((_ nullable.lift +) x y),
   * where x, y of type (Nullable Int), then
   * kind would be ADD, and args would be [x, y].
   * This function would return
   * (nullable.lift (lambda ((a Int) (b Int)) (+ a b)) x y)
   * @param kind The lifted operator.
   * @param args The arguments of the lifted operator.
   * @return A term of Kind NULLABLE_LIFT where the first child
   * is a lambda expression, and the remaining children are
   * the original arguments.
   */
  public Term mkNullableLift(Kind kind, Term[] args)
  {
    MemorySegment[] termPointers = Utils.getHandles(args);
    MemorySegment termPointer = mkNullableLift(handle(), kind.getValue(), termPointers);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkNullableLift(
      MemorySegment pointer, int kindValue, MemorySegment[] termPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_nullable_lift(
          pointer, kindValue, termPointers.length, Native.allocateHandles(arena, termPointers)));
    }
  }

  /* .................................................................... */
  /* Create Operators                                                     */
  /* .................................................................... */

  /**
   * Create an operator for a builtin Kind
   * The Kind may not be the Kind for an indexed operator
   * (e.g., {@link Kind#BITVECTOR_EXTRACT}).
   *
   * @api.note In this case, the Op simply wraps the Kind. The Kind can be used
   *          in mkTerm directly without creating an op first.
   *
   * @param kind The kind to wrap.
   * @return The operator.
   */
  public Op mkOp(Kind kind)
  {
    MemorySegment opPointer = mkOp(handle(), kind.getValue());
    return new Op(ctx, opPointer);
  }

  private MemorySegment mkOp(MemorySegment pointer, int kindValue)
  {
    return Native.handle(CApi.cvc5_mk_op(pointer, kindValue, 0, MemorySegment.NULL));
  }
  /**
   * Create operator of kind:
   * <ul>
   *   <li>
   *     {@link Kind#DIVISIBLE} (to support arbitrary precision integers)
   *   </li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   * @param kind The kind of the operator.
   * @param arg The string argument to this operator.
   * @return The operator.
   */
  public Op mkOp(Kind kind, String arg)
  {
    MemorySegment opPointer = mkOp(handle(), kind.getValue(), arg);
    return new Op(ctx, opPointer);
  }

  private MemorySegment mkOp(MemorySegment pointer, int kindValue, String arg)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_op_from_str(pointer, kindValue, arena.allocateFrom(arg)));
    }
  }

  /**
   * Create operator of kind:
   * <ul>
   *   <li>DIVISIBLE</li>
   *   <li>BITVECTOR_REPEAT</li>
   *   <li>BITVECTOR_ZERO_EXTEND</li>
   *   <li>BITVECTOR_SIGN_EXTEND</li>
   *   <li>BITVECTOR_ROTATE_LEFT</li>
   *   <li>BITVECTOR_ROTATE_RIGHT</li>
   *   <li>INT_TO_BITVECTOR</li>
   *   <li>FLOATINGPOINT_TO_UBV</li>
   *   <li>FLOATINGPOINT_TO_UBV_TOTAL</li>
   *   <li>FLOATINGPOINT_TO_SBV</li>
   *   <li>FLOATINGPOINT_TO_SBV_TOTAL</li>
   *   <li>TUPLE_UPDATE</li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   * @param kind The kind of the operator.
   * @param arg The unsigned int argument to this operator.
   * @return The operator.
   * @throws CVC5ApiException on error
   */
  public Op mkOp(Kind kind, int arg) throws CVC5ApiException
  {
    Utils.validateUnsigned(arg, "arg");
    MemorySegment opPointer = mkOp(handle(), kind.getValue(), arg);
    return new Op(ctx, opPointer);
  }

  private MemorySegment mkOp(MemorySegment pointer, int kindValue, int arg)
  {
    return mkOp(pointer, kindValue, new int[] {arg});
  }

  /**
   * Create operator of Kind:
   * <ul>
   *   <li>BITVECTOR_EXTRACT</li>
   *   <li>FLOATINGPOINT_TO_FP_FROM_IEEE_BV</li>
   *   <li>FLOATINGPOINT_TO_FP_FROM_FP</li>
   *   <li>FLOATINGPOINT_TO_FP_FROM_REAL</li>
   *   <li>FLOATINGPOINT_TO_FP_FROM_SBV</li>
   *   <li>FLOATINGPOINT_TO_FP_FROM_UBV</li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   * @param kind The kind of the operator.
   * @param arg1 The first unsigned int argument to this operator.
   * @param arg2 The second unsigned int argument to this operator.
   * @return The operator.
   * @throws CVC5ApiException on error
   */
  public Op mkOp(Kind kind, int arg1, int arg2) throws CVC5ApiException
  {
    Utils.validateUnsigned(arg1, "arg1");
    Utils.validateUnsigned(arg2, "arg2");
    MemorySegment opPointer = mkOp(handle(), kind.getValue(), arg1, arg2);
    return new Op(ctx, opPointer);
  }

  private MemorySegment mkOp(MemorySegment pointer, int kindValue, int arg1, int arg2)
  {
    return mkOp(pointer, kindValue, new int[] {arg1, arg2});
  }

  /**
   * Create operator of Kind:
   * <ul>
   *   <li>TUPLE_PROJECT</li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   * @param kind The kind of the operator.
   * @param args The arguments (indices) of the operator.
   * @return The operator.
   * @throws CVC5ApiException on error
   */
  public Op mkOp(Kind kind, int[] args) throws CVC5ApiException
  {
    Utils.validateUnsigned(args, "args");
    MemorySegment opPointer = mkOp(handle(), kind.getValue(), args);
    return new Op(ctx, opPointer);
  }

  private MemorySegment mkOp(MemorySegment pointer, int kindValue, int[] args)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(
          CApi.cvc5_mk_op(pointer, kindValue, args.length, Native.allocateInts(arena, args)));
    }
  }

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */

  /**
   * Create a Boolean {@code true} constant.
   * @return The true constant.
   */
  public Term mkTrue()
  {
    MemorySegment termPointer = mkTrue(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkTrue(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_true(pointer));
  }
  /**
   * Create a Boolean {@code false} constant.
   * @return The false constant.
   */
  public Term mkFalse()
  {
    MemorySegment termPointer = mkFalse(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFalse(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_false(pointer));
  }
  /**
   * Create a Boolean constant.
   * @param val The value of the constant.
   * @return The Boolean constant.
   */
  public Term mkBoolean(boolean val)
  {
    MemorySegment termPointer = mkBoolean(handle(), val);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkBoolean(MemorySegment pointer, boolean val)
  {
    return Native.handle(CApi.cvc5_mk_boolean(pointer, val));
  }
  /**
   * Create a constant representing the number Pi.
   * @return A constant representing Pi.
   */
  public Term mkPi()
  {
    MemorySegment termPointer = mkPi(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkPi(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_pi(pointer));
  }
  /**
   * Create an integer constant from a string.
   * @param s The string representation of the constant, may represent an.
   *          integer (e.g., "123").
   * @return A constant of sort Integer assuming {@code s} represents an
   *         integer).
   * @throws CVC5ApiException on error
   */
  public Term mkInteger(String s) throws CVC5ApiException
  {
    MemorySegment termPointer = mkInteger(handle(), s);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkInteger(MemorySegment pointer, String s) throws CVC5ApiException
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_integer(pointer, arena.allocateFrom(s)));
    }
  }

  /**
   * Create an integer constant from a C++ {@code int}.
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  public Term mkInteger(long val)
  {
    MemorySegment termPointer = mkInteger(handle(), val);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkInteger(MemorySegment pointer, long val)
  {
    return Native.handle(CApi.cvc5_mk_integer_int64(pointer, val));
  }
  /**
   * Create a real constant from a string.
   * @param s The string representation of the constant, may represent an.
   *          integer (e.g., "123") or real constant (e.g., "12.34" or
   * "12/34").
   * @return A constant of sort Real.
   * @throws CVC5ApiException on error
   */
  public Term mkReal(String s) throws CVC5ApiException
  {
    MemorySegment termPointer = mkReal(handle(), s);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkReal(MemorySegment pointer, String s) throws CVC5ApiException
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_real(pointer, arena.allocateFrom(s)));
    }
  }
  /**
   * Create a real constant from an integer.
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  public Term mkReal(long val)
  {
    MemorySegment termPointer = mkRealValue(handle(), val);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkRealValue(MemorySegment pointer, long val)
  {
    return Native.handle(CApi.cvc5_mk_real_int64(pointer, val));
  }
  /**
   * Create a real constant from a rational.
   * @param num The value of the numerator.
   * @param den The value of the denominator.
   * @return A constant of sort Real.
   */
  public Term mkReal(long num, long den)
  {
    MemorySegment termPointer = mkReal(handle(), num, den);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkReal(MemorySegment pointer, long num, long den)
  {
    return Native.handle(CApi.cvc5_mk_real_num_den(pointer, num, den));
  }

  /**
   * Create a regular expression none ({@code re.none}) term.
   * @return The none term.
   */
  public Term mkRegexpNone()
  {
    MemorySegment termPointer = mkRegexpNone(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkRegexpNone(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_regexp_none(pointer));
  }

  /**
   * Create a regular expression all ({@code re.all}) term.
   * @return The all term.
   */
  public Term mkRegexpAll()
  {
    MemorySegment termPointer = mkRegexpAll(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkRegexpAll(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_regexp_all(pointer));
  }

  /**
   * Create a regular expression allchar ({@code re.allchar}) term.
   * @return The allchar term.
   */
  public Term mkRegexpAllchar()
  {
    MemorySegment termPointer = mkRegexpAllchar(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkRegexpAllchar(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_regexp_allchar(pointer));
  }

  /**
   * Create a constant representing an empty set of the given sort.
   * @param sort The sort of the set elements.
   * @return The empty set constant.
   */
  public Term mkEmptySet(Sort sort)
  {
    MemorySegment termPointer = mkEmptySet(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkEmptySet(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_empty_set(pointer, sortPointer));
  }
  /**
   * Create a constant representing an empty bag of the given sort.
   * @param sort The sort of the bag elements.
   * @return The empty bag constant.
   */
  public Term mkEmptyBag(Sort sort)
  {
    MemorySegment termPointer = mkEmptyBag(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkEmptyBag(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_empty_bag(pointer, sortPointer));
  }

  /**
   * Create a separation logic empty term.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The separation logic empty term.
   */
  public Term mkSepEmp()
  {
    MemorySegment termPointer = mkSepEmp(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkSepEmp(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_mk_sep_emp(pointer));
  }

  /**
   * Create a separation logic nil term.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sort The sort of the nil term.
   * @return The separation logic nil term.
   */
  public Term mkSepNil(Sort sort)
  {
    MemorySegment termPointer = mkSepNil(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkSepNil(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_sep_nil(pointer, sortPointer));
  }

  /**
   * Create a String constant.
   * @param s The string this constant represents.
   * @return The String constant.
   */
  public Term mkString(String s)
  {
    return mkString(s, false);
  }

  /**
   * Create a String constant.
   * @param s The string this constant represents.
   * @param useEscSequences Determines whether escape sequences in {@code s}
   *                        should be converted to the corresponding unicode
   *                        character.
   * @return The String constant.
   */
  public Term mkString(String s, boolean useEscSequences)
  {
    // TODO: review unicode https://github.com/cvc5/cvc5-wishues/issues/150
    MemorySegment termPointer = mkString(handle(), s, useEscSequences);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkString(MemorySegment pointer, String s, boolean useEscSequences)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_string(pointer, arena.allocateFrom(s), useEscSequences));
    }
  }

  /**
   * Create a String constant.
   * @param s A list of unsigned (unicode) values this constant represents
   *          as string.
   * @return The String constant.
   * @throws CVC5ApiException on error
   */
  public Term mkString(int[] s) throws CVC5ApiException
  {
    Utils.validateUnsigned(s, "s");
    MemorySegment termPointer = mkString(handle(), s);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkString(MemorySegment pointer, int[] s)
  {
    try (Arena arena = Arena.ofConfined())
    {
      // a NUL-terminated UTF-32 string
      MemorySegment chars = Native.allocateInts(arena, Arrays.copyOf(s, s.length + 1));
      return Native.handle(CApi.cvc5_mk_string_from_char32(pointer, chars));
    }
  }

  /**
   * Create an empty sequence of the given element sort.
   * @param sort The element sort of the sequence.
   * @return The empty sequence with given element sort.
   */
  public Term mkEmptySequence(Sort sort)
  {
    MemorySegment termPointer = mkEmptySequence(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkEmptySequence(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_empty_sequence(pointer, sortPointer));
  }

  /**
   * Create a universe set of the given sort.
   * @param sort The sort of the set elements.
   * @return The universe set constant.
   */
  public Term mkUniverseSet(Sort sort)
  {
    MemorySegment termPointer = mkUniverseSet(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkUniverseSet(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_universe_set(pointer, sortPointer));
  }

  /**
   * Create a bit-vector constant of given size and value = 0.
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector constant.
   * @throws CVC5ApiException on error
   */
  public Term mkBitVector(int size) throws CVC5ApiException
  {
    return mkBitVector(size, 0);
  }

  /**
   * Create a bit-vector constant of given size and value.
   *
   * @api.note The given value must fit into a bit-vector of the given size.
   *
   * @param size The bit-width of the bit-vector sort.
   * @param val The value of the constant.
   * @return The bit-vector constant.
   * @throws CVC5ApiException on error
   */
  public Term mkBitVector(int size, long val) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    Utils.validateUnsigned(val, "val");
    MemorySegment termPointer = mkBitVector(handle(), size, val);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkBitVector(MemorySegment pointer, int size, long val)
  {
    return Native.handle(CApi.cvc5_mk_bv_uint64(pointer, size, val));
  }

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * @api.note The given value must fit into a bit-vector of the given size.
   *
   * @param size The bit-width of the constant.
   * @param s The string representation of the constant.
   * @param base The base of the string representation (2, 10, or 16)
   * @return The bit-vector constant.
   * @throws CVC5ApiException on error
   */
  public Term mkBitVector(int size, String s, int base) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    Utils.validateUnsigned(base, "base");
    MemorySegment termPointer = mkBitVector(handle(), size, s, base);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkBitVector(MemorySegment pointer, int size, String s, int base)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_bv(pointer, size, arena.allocateFrom(s), base));
    }
  }

  /**
   * Create a finite field constant in a given field and for a given value.
   *
   * @api.note The given value must fit into a the given finite field.
   *
   * @param val The value of the constant.
   * @param sort The sort of the finite field.
   * @param base The base of the string representation.
   * @return The finite field constant.
   * @throws CVC5ApiException on error
   */
  public Term mkFiniteFieldElem(String val, Sort sort, int base) throws CVC5ApiException
  {
    MemorySegment termPointer = mkFiniteFieldElem(handle(), val, sort.handle(), base);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFiniteFieldElem(
      MemorySegment pointer, String val, MemorySegment sortPointer, int base)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(
          CApi.cvc5_mk_ff_elem(pointer, arena.allocateFrom(val), sortPointer, base));
    }
  }

  /**
   * Create a constant array with the provided constant value stored at
   * every index
   * @param sort The sort of the constant array (must be an array sort)
   * @param val The constant value to store (must match the sort's element
   *            sort).
   * @return The constant array term.
   */
  public Term mkConstArray(Sort sort, Term val)
  {
    MemorySegment termPointer = mkConstArray(handle(), sort.handle(), val.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkConstArray(
      MemorySegment pointer, MemorySegment sortPointer, MemorySegment valPointer)
  {
    return Native.handle(CApi.cvc5_mk_const_array(pointer, sortPointer, valPointer));
  }
  /**
   * Create a positive infinity floating-point constant (SMT-LIB: {@code +oo}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPointPosInf(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment termPointer = mkFloatingPointPosInf(handle(), exp, sig);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPointPosInf(MemorySegment pointer, int exp, int sig)
  {
    return Native.handle(CApi.cvc5_mk_fp_pos_inf(pointer, exp, sig));
  }
  /**
   * Create a negative infinity floating-point constant (SMT-LIB: {@code -oo}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPointNegInf(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment termPointer = mkFloatingPointNegInf(handle(), exp, sig);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPointNegInf(MemorySegment pointer, int exp, int sig)
  {
    return Native.handle(CApi.cvc5_mk_fp_neg_inf(pointer, exp, sig));
  }
  /**
   * Create a not-a-number floating-point constant (SMT-LIB: {@code NaN}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPointNaN(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment termPointer = mkFloatingPointNaN(handle(), exp, sig);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPointNaN(MemorySegment pointer, int exp, int sig)
  {
    return Native.handle(CApi.cvc5_mk_fp_nan(pointer, exp, sig));
  }

  /**
   * Create a positive zero floating-point constant (SMT-LIB: {@code +zero}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPointPosZero(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment termPointer = mkFloatingPointPosZero(handle(), exp, sig);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPointPosZero(MemorySegment pointer, int exp, int sig)
  {
    return Native.handle(CApi.cvc5_mk_fp_pos_zero(pointer, exp, sig));
  }

  /**
   * Create a negative zero floating-point constant (SMT-LIB: {@code -zero}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPointNegZero(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment termPointer = mkFloatingPointNegZero(handle(), exp, sig);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPointNegZero(MemorySegment pointer, int exp, int sig)
  {
    return Native.handle(CApi.cvc5_mk_fp_neg_zero(pointer, exp, sig));
  }

  /**
   * Create a rounding mode constant.
   * @param rm The floating point rounding mode this constant represents.
   * @return The rounding mode.
   */
  public Term mkRoundingMode(RoundingMode rm)
  {
    MemorySegment termPointer = mkRoundingMode(handle(), rm.getValue());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkRoundingMode(MemorySegment pointer, int rm)
  {
    return Native.handle(CApi.cvc5_mk_rm(pointer, rm));
  }

  /**
   * Create a floating-point value from a bit-vector given in IEEE-754
   * format.
   * @param exp Size of the exponent.
   * @param sig Size of the significand.
   * @param val Value of the floating-point constant as a bit-vector term.
   * @return The floating-point value.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPoint(int exp, int sig, Term val) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    MemorySegment termPointer = mkFloatingPoint(handle(), exp, sig, val.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPoint(
      MemorySegment pointer, int exp, int sig, MemorySegment valPointer)
  {
    return Native.handle(CApi.cvc5_mk_fp(pointer, exp, sig, valPointer));
  }

  /**
   * Create a floating-point value from its three IEEE-754 bit-vector value
   * components (sign bit, exponent, significand).
   * @param sign The sign bit.
   * @param exp  The bit-vector representing the exponent.
   * @param sig The bit-vector representing the significand.
   * @return The floating-point value.
   * @throws CVC5ApiException on error
   */
  public Term mkFloatingPoint(Term sign, Term exp, Term sig) throws CVC5ApiException
  {
    MemorySegment termPointer =
        mkFloatingPointX(handle(), sign.handle(), exp.handle(), sig.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkFloatingPointX(MemorySegment pointer,
      MemorySegment signPointer,
      MemorySegment expPointer,
      MemorySegment sigPointer)
  {
    return Native.handle(CApi.cvc5_mk_fp_from_ieee(pointer, signPointer, expPointer, sigPointer));
  }

  /**
   * Create a cardinality constraint for an uninterpreted sort.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sort The sort the cardinality constraint is for.
   * @param upperBound The upper bound on the cardinality of the sort.
   * @return The cardinality constraint.
   * @throws CVC5ApiException on error
   */
  public Term mkCardinalityConstraint(Sort sort, int upperBound) throws CVC5ApiException
  {
    Utils.validateUnsigned(upperBound, "upperBound");
    MemorySegment termPointer = mkCardinalityConstraint(handle(), sort.handle(), upperBound);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkCardinalityConstraint(
      MemorySegment pointer, MemorySegment sortPointer, int upperBound)
  {
    return Native.handle(CApi.cvc5_mk_cardinality_constraint(pointer, sortPointer, upperBound));
  }

  /* .................................................................... */
  /* Create Variables                                                     */
  /* .................................................................... */

  /**
   * Create a free constant.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-const <symbol> <sort> )
   *   ( declare-fun <symbol> ( ) <sort> )
   * }
   *
   * @param sort The sort of the constant.
   * @param symbol The name of the constant.
   * @return The first-order constant.
   */
  public Term mkConst(Sort sort, String symbol)
  {
    MemorySegment termPointer = mkConst(handle(), sort.handle(), symbol);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkConst(MemorySegment pointer, MemorySegment sortPointer, String symbol)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_const(pointer, sortPointer, arena.allocateFrom(symbol)));
    }
  }

  /**
   * Create a free constant with a default symbol name.
   *
   * @param sort The sort of the constant.
   * @return The first-order constant.
   */
  public Term mkConst(Sort sort)
  {
    MemorySegment termPointer = mkConst(handle(), sort.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkConst(MemorySegment pointer, MemorySegment sortPointer)
  {
    return Native.handle(CApi.cvc5_mk_const(pointer, sortPointer, MemorySegment.NULL));
  }

  /**
   * Create a bound variable to be used in a binder (i.e., a quantifier, a
   * lambda, or a witness binder).
   * @param sort The sort of the variable.
   * @return The variable.
   */
  public Term mkVar(Sort sort)
  {
    return mkVar(sort, "");
  }

  /**
   * Create a bound variable to be used in a binder (i.e., a quantifier, a
   * lambda, or a witness binder).
   * @param sort The sort of the variable.
   * @param symbol The name of the variable.
   * @return The variable.
   */
  public Term mkVar(Sort sort, String symbol)
  {
    MemorySegment termPointer = mkVar(handle(), sort.handle(), symbol);
    return new Term(ctx, termPointer);
  }

  private MemorySegment mkVar(MemorySegment pointer, MemorySegment sortPointer, String symbol)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_var(pointer, sortPointer, arena.allocateFrom(symbol)));
    }
  }

  /* .................................................................... */
  /* Create datatype constructor declarations                             */
  /* .................................................................... */

  /**
   * Create a datatype constructor declaration.
   * @param name The name of the datatype constructor.
   * @return The DatatypeConstructorDecl.
   */
  public DatatypeConstructorDecl mkDatatypeConstructorDecl(String name)
  {
    MemorySegment declPointer = mkDatatypeConstructorDecl(handle(), name);
    return new DatatypeConstructorDecl(ctx, declPointer);
  }

  private MemorySegment mkDatatypeConstructorDecl(MemorySegment pointer, String name)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_dt_cons_decl(pointer, arena.allocateFrom(name)));
    }
  }

  /* .................................................................... */
  /* Create datatype declarations                                         */
  /* .................................................................... */

  /**
   * Create a datatype declaration.
   * @param name The name of the datatype.
   * @return The DatatypeDecl.
   */
  public DatatypeDecl mkDatatypeDecl(String name)
  {
    return mkDatatypeDecl(name, false);
  }

  /**
   * Create a datatype declaration.
   * @param name The name of the datatype.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  public DatatypeDecl mkDatatypeDecl(String name, boolean isCoDatatype)
  {
    MemorySegment declPointer = mkDatatypeDecl(handle(), name, isCoDatatype);
    return new DatatypeDecl(ctx, declPointer);
  }

  private MemorySegment mkDatatypeDecl(MemorySegment pointer, String name, boolean isCoDatatype)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_dt_decl(pointer, arena.allocateFrom(name), isCoDatatype));
    }
  }

  /**
   * Create a datatype declaration.
   *
   * Create sorts parameter with {@link TermManager#mkParamSort(String)}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @return The DatatypeDecl.
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params)
  {
    return mkDatatypeDecl(name, params, false);
  }

  /**
   * Create a datatype declaration.
   *
   * Create sorts parameter with {@link TermManager#mkParamSort(String)}.
   *
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params, boolean isCoDatatype)
  {
    MemorySegment[] paramPointers = Utils.getHandles(params);
    MemorySegment declPointer = mkDatatypeDecl(handle(), name, paramPointers, isCoDatatype);
    return new DatatypeDecl(ctx, declPointer);
  }

  private MemorySegment mkDatatypeDecl(
      MemorySegment pointer, String name, MemorySegment[] paramPointers, boolean isCoDatatype)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_dt_decl_with_params(pointer,
          arena.allocateFrom(name),
          paramPointers.length,
          Native.allocateHandles(arena, paramPointers),
          isCoDatatype));
    }
  }
}
