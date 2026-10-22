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

import io.github.cvc5.capi.CApi;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.util.List;
import java.util.function.BinaryOperator;

/**
 * The sort of a cvc5 term.
 */
public class Sort extends AbstractPointer implements Comparable<Sort>
{
  /**
   * Null sort
   */
  public Sort()
  {
    super(null, MemorySegment.NULL, null);
  }

  Sort(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, Sort::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_sort_release(pointer);
  }

  /**
   * Call a function of the C API that returns an array of sorts, such as
   * {@code cvc5_sort_fun_get_domain}, and copy the result.
   *
   * @param pointer The sort to pass to the function.
   * @param function The function, which takes the sort and the
   *                 {@code size_t} output parameter for the size of the array,
   *                 and returns the array.
   * @return The sorts of the array, which are owned by the caller.
   */
  private static MemorySegment[] sortArray(
      MemorySegment pointer, BinaryOperator<MemorySegment> function)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment sorts = Native.check(function.apply(pointer, size));
      return Native.handles(sorts, size.get(JAVA_LONG, 0));
    }
  }

  /**
   * Throw a {@link CVC5ApiException}, even where it is not declared, like the
   * errors of the C API. For errors that the C++ API reports but the C API
   * does not check.
   *
   * @param message The error message.
   * @return Never returns normally.
   */
  @SuppressWarnings("unchecked")
  private static <T extends Throwable> T apiError(String message) throws T
  {
    T error = (T) new CVC5ApiException(message);
    throw error;
  }

  // endregion

  /**
   * Comparison for structural equality.
   * @param s The sort to compare to.
   * @return True if the sorts are equal.
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
    Sort sort = (Sort) s;
    if (address() == sort.address())
    {
      return true;
    }
    return equals(handle(), sort.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_sort_is_equal(pointer1, pointer2));
  }

  /**
   * Comparison for ordering on sorts.
   *
   * @param s The sort to compare to.
   * @return A negative integer, zero, or a positive integer as this sort
   *         is less than, equal to, or greater than the specified sort.
   */
  @Override
  public int compareTo(Sort s)
  {
    return this.compareTo(handle(), s.handle());
  }

  private int compareTo(MemorySegment pointer1, MemorySegment pointer2)
  {
    if (pointer1.address() == 0 || pointer2.address() == 0)
    {
      // The C API rejects null sorts, which the C++ API orders before all
      // other sorts.
      return Boolean.compare(pointer1.address() != 0, pointer2.address() != 0);
    }
    return (int) Native.check(CApi.cvc5_sort_compare(pointer1, pointer2));
  }

  /**
   * Get the kind of this sort.
   *
   * @return The kind of this sort.
   * @api.note This method is experimental and may change in future versions.
   * @throws CVC5ApiException on error
   */
  public SortKind getKind() throws CVC5ApiException
  {
    int value = getKind(handle());
    return SortKind.fromInt(value);
  }

  private int getKind(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_get_kind(pointer));
  }

  /**
   * Determine if the sort has a symbol.
   * @return True if the sort has a symbol.
   */
  public boolean hasSymbol()
  {
    return hasSymbol(handle());
  }

  private boolean hasSymbol(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // The C API returns false for the null sort, which the C++ API rejects.
      throw apiError("invalid sort");
    }
    return Native.check(CApi.cvc5_sort_has_symbol(pointer));
  }

  /**
   * Get the raw symbol of the symbol.
   *
   * @api.note Asserts hasSymbol().
   * @return The raw symbol of the symbol.
   */
  public String getSymbol()
  {
    return getSymbol(handle());
  }

  private String getSymbol(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_sort_get_symbol(pointer));
  }

  /**
   * Determine if this is the null sort.
   * @return True if this Sort is the null sort.
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
   * Determine if this is the Boolean sort (SMT-LIB: {@code Bool}).
   * @return True if this sort is the Boolean sort.
   */
  public boolean isBoolean()
  {
    return isBoolean(handle());
  }

  private boolean isBoolean(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_boolean(pointer));
  }

  /**
   * Determine if this is the integer sort (SMT-LIB: {@code Int}).
   * @return True if this sort is the integer sort.
   */
  public boolean isInteger()
  {
    return isInteger(handle());
  }

  private boolean isInteger(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_integer(pointer));
  }

  /**
   * Determine if this is the real sort (SMT-LIB: {@code Real}).
   * @return True if this sort is the real sort.
   */
  public boolean isReal()
  {
    return isReal(handle());
  }

  private boolean isReal(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_real(pointer));
  }

  /**
   * Determine if this is the string sort (SMT-LIB: {@code String})..
   * @return True if this sort is the string sort.
   */
  public boolean isString()
  {
    return isString(handle());
  }

  private boolean isString(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_string(pointer));
  }

  /**
   * Determine if this is the regular expression sort (SMT-LIB: {@code RegLan}).
   * @return True if this sort is the regular expression sort.
   */
  public boolean isRegExp()
  {
    return isRegExp(handle());
  }

  private boolean isRegExp(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_regexp(pointer));
  }

  /**
   * Determine if this is the rounding mode sort (SMT-LIB: {@code RoundingMode}).
   * @return True if this sort is the rounding mode sort.
   */
  public boolean isRoundingMode()
  {
    return isRoundingMode(handle());
  }

  private boolean isRoundingMode(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_rm(pointer));
  }

  /**
   * Determine if this is a bit-vector sort (SMT-LIB: {@code (_ BitVec i)}).
   * @return True if this sort is a bit-vector sort.
   */
  public boolean isBitVector()
  {
    return isBitVector(handle());
  }

  private boolean isBitVector(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_bv(pointer));
  }

  /**
   * Determine if this is a finite field sort (SMT-LIB: {@code (_ FiniteField i)}).
   * @return True if this sort is a finite field sort.
   */
  public boolean isFiniteField()
  {
    return isFiniteField(handle());
  }

  private boolean isFiniteField(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_ff(pointer));
  }

  /**
   * Determine if this is a floatingpoint sort
   * (SMT-LIB: {@code (_ FloatingPoint eb sb)}).
   * @return True if this sort is a floating-point sort.
   */
  public boolean isFloatingPoint()
  {
    return isFloatingPoint(handle());
  }

  private boolean isFloatingPoint(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_fp(pointer));
  }

  /**
   * Determine if this is a datatype sort.
   * @return True if this sort is a datatype sort.
   */
  public boolean isDatatype()
  {
    return isDatatype(handle());
  }

  private boolean isDatatype(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_dt(pointer));
  }

  /**
   * Determine if this is a datatype constructor sort.
   * @return True if this sort is a datatype constructor sort.
   */
  public boolean isDatatypeConstructor()
  {
    return isDatatypeConstructor(handle());
  }

  private boolean isDatatypeConstructor(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_dt_constructor(pointer));
  }

  /**
   * Determine if this is a datatype selector sort.
   * @return True if this sort is a datatype selector sort.
   */
  public boolean isDatatypeSelector()
  {
    return isDatatypeSelector(handle());
  }

  private boolean isDatatypeSelector(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_dt_selector(pointer));
  }

  /**
   * Determine if this is a datatype tester sort.
   * @return True if this sort is a datatype tester sort.
   */
  public boolean isDatatypeTester()
  {
    return isDatatypeTester(handle());
  }

  private boolean isDatatypeTester(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_dt_tester(pointer));
  }

  /**
   * Determine if this is a datatype updater sort.
   * @return True if this sort is a datatype updater sort.
   */
  public boolean isDatatypeUpdater()
  {
    return isDatatypeUpdater(handle());
  }

  private boolean isDatatypeUpdater(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_dt_updater(pointer));
  }

  /**
   * Determine if this is a function sort.
   * @return True if this sort is a function sort.
   */
  public boolean isFunction()
  {
    return isFunction(handle());
  }

  private boolean isFunction(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_fun(pointer));
  }

  /**
   * Determine if this is a predicate sort.
   *
   * A predicate sort is a function sort that maps to the Boolean sort. All
   * predicate sorts are also function sorts.
   *
   * @return True if this sort is a predicate sort.
   */
  public boolean isPredicate()
  {
    return isPredicate(handle());
  }

  private boolean isPredicate(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_predicate(pointer));
  }

  /**
   * Determine if this a tuple sort.
   * @return True if this sort is a tuple sort.
   */
  public boolean isTuple()
  {
    return isTuple(handle());
  }

  private boolean isTuple(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_tuple(pointer));
  }

  /**
   * Determine if this a nullable sort.
   * @return True if this sort is a nullable sort.
   */
  public boolean isNullable()
  {
    return isNullable(handle());
  }

  private boolean isNullable(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_nullable(pointer));
  }

  /**
   * Determine if this is a record sort.
   * @api.note This method is experimental and may change in future versions.
   * @return True if the sort is a record sort.
   */
  public boolean isRecord()
  {
    return isRecord(handle());
  }

  private boolean isRecord(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_record(pointer));
  }

  /**
   * Determine if this is an array sort.
   * @return True if the sort is an array sort.
   */
  public boolean isArray()
  {
    return isArray(handle());
  }

  private boolean isArray(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_array(pointer));
  }

  /**
   * Determine if this is a Set sort.
   * @return True if the sort is a Set sort.
   */
  public boolean isSet()
  {
    return isSet(handle());
  }

  private boolean isSet(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_set(pointer));
  }

  /**
   * Determine if this is a Bag sort.
   * @return True if the sort is a Bag sort.
   */
  public boolean isBag()
  {
    return isBag(handle());
  }

  private boolean isBag(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_bag(pointer));
  }

  /**
   * Determine if this is a Sequence sort.
   * @return True if the sort is a Sequence sort.
   */
  public boolean isSequence()
  {
    return isSequence(handle());
  }

  private boolean isSequence(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_sequence(pointer));
  }

  /**
   * Determine if this is an abstract sort.
   * @return True if the sort is a abstract sort.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public boolean isAbstract()
  {
    return isAbstract(handle());
  }

  private boolean isAbstract(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_abstract(pointer));
  }

  /**
   * Determine if this is an uninterpreted sort.
   * @return True if this is an uninterpreted sort.
   */
  public boolean isUninterpretedSort()
  {
    return isUninterpretedSort(handle());
  }

  private boolean isUninterpretedSort(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_uninterpreted_sort(pointer));
  }

  /**
   * Determine if this is an uninterpreted sort constructor.
   *
   * An uninterpreted sort constructor has arity &gt; 0 and can be instantiated
   * to construct uninterpreted sorts with given sort parameters.
   *
   * @return True if this is a sort constructor kind.
   */
  public boolean isUninterpretedSortConstructor()
  {
    return isUninterpretedSortConstructor(handle());
  }

  private boolean isUninterpretedSortConstructor(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_is_uninterpreted_sort_constructor(pointer));
  }

  /**
   * Determine if this is an instantiated (parametric datatype or uninterpreted
   * sort constructor) sort.
   *
   * An instantiated sort is a sort that has been constructed from
   * instantiating a sort with sort arguments
   * (see {@link Sort#instantiate(Sort[])}).
   *
   * @return True if this is an instantiated sort.
   */
  public boolean isInstantiated()
  {
    return isInstantiated(handle());
  }

  private boolean isInstantiated(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // The C API returns false for the null sort, which the C++ API rejects.
      throw apiError("invalid sort");
    }
    return Native.check(CApi.cvc5_sort_is_instantiated(pointer));
  }

  /**
   * Get the associated uninterpreted sort constructor of an instantiated
   * uninterpreted sort.
   *
   * @return The uninterpreted sort constructor sort.
   */
  public Sort getUninterpretedSortConstructor()
  {
    MemorySegment sortPointer = getUninterpretedSortConstructor(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getUninterpretedSortConstructor(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_get_uninterpreted_sort_constructor(pointer));
  }

  /**
   * Get the underlying datatype of a datatype sort.
   *
   * @return The underlying datatype of a datatype sort.
   */
  public Datatype getDatatype()
  {
    MemorySegment datatypePointer = getDatatype(handle());
    return new Datatype(ctx, datatypePointer);
  }

  private MemorySegment getDatatype(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_get_datatype(pointer));
  }

  /**
   * Instantiate a parameterized datatype sort or uninterpreted sort
   * constructor sort.
   *
   * Create sorts parameter with {@link TermManager#mkParamSort(String)}).
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param params The list of sort parameters to instantiate with.
   * @return The instantiated sort.
   */
  public Sort instantiate(Sort[] params)
  {
    MemorySegment[] paramsPointers = Utils.getHandles(params);
    MemorySegment sortPointer = instantiate(handle(), paramsPointers);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment instantiate(MemorySegment pointer, MemorySegment[] paramsPointers)
  {
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_sort_instantiate(
          pointer, paramsPointers.length, Native.allocateHandles(arena, paramsPointers)));
    }
  }

  /**
   * Get the sorts used to instantiate the sort parameters of a parametric
   * sort (parametric datatype or uninterpreted sort constructor sort,
   * see {@link Sort#instantiate(Sort[])}).
   *
   * @return The sorts used to instantiate the sort parameters of a
   *         parametric sort.
   */
  public Sort[] getInstantiatedParameters()
  {
    MemorySegment[] pointers = getInstantiatedParameters(handle());
    return Utils.getSorts(ctx, pointers);
  }

  private MemorySegment[] getInstantiatedParameters(MemorySegment pointer)
  {
    return sortArray(pointer, CApi::cvc5_sort_get_instantiated_parameters);
  }

  /**
   * Substitution of Sorts.
   *
   * @api.note This replacement is applied during a pre-order traversal and
   * only once to the sort. It is not run until fix point.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sort The subsort to be substituted within this sort.
   * @param replacement The sort replacing the substituted subsort.
   * @return The sort yielded by substituting the replacement sort within the
   *         given sort.
   */
  public Sort substitute(Sort sort, Sort replacement)
  {
    MemorySegment sortPointer = substitute(handle(), sort.handle(), replacement.handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment substitute(
      MemorySegment pointer, MemorySegment sortPointer, MemorySegment replacementPointer)
  {
    return Native.handle(CApi.cvc5_sort_substitute(pointer, sortPointer, replacementPointer));
  }

  /**
   * Simultaneous substitution of Sorts.
   *
   * Note that this replacement is applied during a pre-order traversal and
   * only once to the sort. It is not run until fix point. In the case that
   * sorts contains duplicates, the replacement earliest in the list takes
   * priority.
   *
   * For example,
   * {@code (Array A B).substitute({A, C}, {(Array C D), (Array A B)})} will
   * return {@code (Array (Array C D) B)}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sorts The subsorts to be substituted within this sort.
   * @param replacements The sort replacing the substituted subsorts.
   * @return The sorts yielded by substituting the replacement sort within the
   *         given sorts.
   */
  public Sort substitute(Sort[] sorts, Sort[] replacements)
  {
    MemorySegment[] sortPointers = Utils.getHandles(sorts);
    MemorySegment[] replacementPointers = Utils.getHandles(sorts);
    MemorySegment sortPointer = substitute(handle(), sortPointers, replacementPointers);
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment substitute(
      MemorySegment pointer, MemorySegment[] sortPointers, MemorySegment[] replacementPointers)
  {
    if (sortPointers.length != replacementPointers.length)
    {
      // The C API takes a single size for both arrays.
      throw apiError("expected vectors of the same arity in substitute");
    }
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_sort_substitute_sorts(pointer,
          sortPointers.length,
          Native.allocateHandles(arena, sortPointers),
          Native.allocateHandles(arena, replacementPointers)));
    }
  }

  /**
   * @return A string representation of this sort.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      return "null";
    }
    return Native.string(CApi.cvc5_sort_to_string(MemorySegment.ofAddress(pointer)));
  }

  /* Constructor sort ------------------------------------------------------- */

  /**
   * Get the arity of a datatype constructor sort.
   *
   * @return The arity of a datatype constructor sort.
   */
  public int getDatatypeConstructorArity()
  {
    return getDatatypeConstructorArity(handle());
  }

  private int getDatatypeConstructorArity(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_sort_dt_constructor_get_arity(pointer));
  }

  /**
   * Get the domain sorts of a datatype constructor sort.
   *
   * @return The domain sorts of a datatype constructor sort.
   */
  public Sort[] getDatatypeConstructorDomainSorts()
  {
    MemorySegment[] pointers = getDatatypeConstructorDomainSorts(handle());
    return Utils.getSorts(ctx, pointers);
  }

  private MemorySegment[] getDatatypeConstructorDomainSorts(MemorySegment pointer)
  {
    return sortArray(pointer, CApi::cvc5_sort_dt_constructor_get_domain);
  }

  /**
   * Get the codomain sort of a datatype constructor sort.
   *
   * @return The codomain sort of a datatype constructor sort.
   */
  public Sort getDatatypeConstructorCodomainSort()
  {
    MemorySegment sortPointer = getDatatypeConstructorCodomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getDatatypeConstructorCodomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_dt_constructor_get_codomain(pointer));
  }

  /* Selector sort ------------------------------------------------------- */

  /**
   * Get the domain sort of a datatype selector sort.
   * @return The domain sort of a datatype selector sort.
   */
  public Sort getDatatypeSelectorDomainSort()
  {
    MemorySegment sortPointer = getDatatypeSelectorDomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getDatatypeSelectorDomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_dt_selector_get_domain(pointer));
  }

  /**
   * Get the codomain sort of a datatype selector sort.
   *
   * @return The codomain sort of a datatype selector sort.
   */
  public Sort getDatatypeSelectorCodomainSort()
  {
    MemorySegment sortPointer = getDatatypeSelectorCodomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getDatatypeSelectorCodomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_dt_selector_get_codomain(pointer));
  }

  /* Tester sort ------------------------------------------------------- */

  /**
   * Get the domain sort of a datatype tester sort.
   *
   * @return The domain sort of a datatype tester sort.
   */
  public Sort getDatatypeTesterDomainSort()
  {
    MemorySegment sortPointer = getDatatypeTesterDomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getDatatypeTesterDomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_dt_tester_get_domain(pointer));
  }

  /**
   * Get the codomain sort of a datatype tester sort, which is the Boolean sort.
   *
   * @return The codomain sort of a datatype tester sort, which is the Boolean
   *         sort.
   */
  public Sort getDatatypeTesterCodomainSort()
  {
    MemorySegment sortPointer = getDatatypeTesterCodomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getDatatypeTesterCodomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_dt_tester_get_codomain(pointer));
  }

  /* Function sort ------------------------------------------------------- */

  /**
   * Get the arity of a function sort.
   *
   * @return The arity of a function sort.
   */
  public int getFunctionArity()
  {
    return getFunctionArity(handle());
  }

  private int getFunctionArity(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_sort_fun_get_arity(pointer));
  }

  /**
   * Get the domain sorts of a function sort.
   *
   * @return The domain sorts of a function sort.
   */
  public Sort[] getFunctionDomainSorts()
  {
    MemorySegment[] pointers = getFunctionDomainSorts(handle());
    return Utils.getSorts(ctx, pointers);
  }

  private MemorySegment[] getFunctionDomainSorts(MemorySegment pointer)
  {
    return sortArray(pointer, CApi::cvc5_sort_fun_get_domain);
  }

  /**
   * Get the codomain sort of a function sort.
   *
   * @return The codomain sort of a function sort.
   */
  public Sort getFunctionCodomainSort()
  {
    MemorySegment sortPointer = getFunctionCodomainSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getFunctionCodomainSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_fun_get_codomain(pointer));
  }

  /* Array sort ---------------------------------------------------------- */

  /**
   * Get the array index sort of an array sort.
   * @return The array index sort of an array sort.
   */
  public Sort getArrayIndexSort()
  {
    MemorySegment sortPointer = getArrayIndexSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getArrayIndexSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_array_get_index_sort(pointer));
  }

  /**
   * Get the array element sort of an array element sort.
   *
   * @return The array element sort of an array element sort.
   */
  public Sort getArrayElementSort()
  {
    MemorySegment sortPointer = getArrayElementSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getArrayElementSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_array_get_element_sort(pointer));
  }

  /* Set sort ------------------------------------------------------------ */

  /**
   * Get the element sort of a set sort.
   *
   * @return The element sort of a set sort.
   */
  public Sort getSetElementSort()
  {
    MemorySegment sortPointer = getSetElementSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getSetElementSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_set_get_element_sort(pointer));
  }

  /* Bag sort ------------------------------------------------------------ */

  /**
   * Get the element sort of a bag sort.
   *
   * @return The element sort of a bag sort.
   */
  public Sort getBagElementSort()
  {
    MemorySegment sortPointer = getBagElementSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getBagElementSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_bag_get_element_sort(pointer));
  }

  /* Sequence sort ------------------------------------------------------- */

  /**
   * Get the element sort of a sequence sort.
   *
   * @return The element sort of a sequence sort.
   */
  public Sort getSequenceElementSort()
  {
    MemorySegment sortPointer = getSequenceElementSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getSequenceElementSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_sequence_get_element_sort(pointer));
  }

  /* Abstract sort ------------------------------------------------------- */

  /**
   * Get the sort kind of an abstract sort, which denotes the kind of
   * sorts that this abstract sort denotes.
   *
   * @return The sort kind of an abstract sort, which denotes the kind of
   * sorts that this abstract sort denotes.
   * @throws CVC5ApiException on error
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public SortKind getAbstractedKind() throws CVC5ApiException
  {
    int value = getAbstractedKind(handle());
    return SortKind.fromInt(value);
  }

  private int getAbstractedKind(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_abstract_get_kind(pointer));
  }

  /* Sort constructor sort ----------------------------------------------- */

  /**
   * Get the arity of an uninterpreted sort constructor sort.
   *
   * @return The arity of an uninterpreted sort constructor sort.
   */
  public int getUninterpretedSortConstructorArity()
  {
    return getUninterpretedSortConstructorArity(handle());
  }

  private int getUninterpretedSortConstructorArity(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_sort_uninterpreted_sort_constructor_get_arity(pointer));
  }

  /* Bit-vector sort ----------------------------------------------------- */

  /**
   * Get the bit-width of the bit-vector sort.
   *
   * @return The bit-width of the bit-vector sort.
   */
  public int getBitVectorSize()
  {
    return getBitVectorSize(handle());
  }

  private int getBitVectorSize(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_bv_get_size(pointer));
  }

  /* Finite field sort --------------------------------------------------- */

  /**
   * Get the bit-width of the bit-vector sort.
   *
   * @return The bit-width of the bit-vector sort.
   */
  public String getFiniteFieldSize()
  {
    return getFiniteFieldSize(handle());
  }

  private String getFiniteFieldSize(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_sort_ff_get_size(pointer));
  }

  /* Floating-point sort ------------------------------------------------- */

  /**
   * Get the bit-width of the exponent of the floating-point sort.
   *
   * @return The bit-width of the exponent of the floating-point sort.
   */
  public int getFloatingPointExponentSize()
  {
    return getFloatingPointExponentSize(handle());
  }

  private int getFloatingPointExponentSize(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_fp_get_exp_size(pointer));
  }

  /**
   * Get the width of the significand of the floating-point sort.
   *
   * @return The width of the significand of the floating-point sort.
   */
  public int getFloatingPointSignificandSize()
  {
    return getFloatingPointSignificandSize(handle());
  }

  private int getFloatingPointSignificandSize(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_sort_fp_get_sig_size(pointer));
  }

  /* Datatype sort ------------------------------------------------------- */

  /**
   * Get the arity of a datatype sort.
   *
   * @return The arity of a datatype sort.
   */
  public int getDatatypeArity()
  {
    return getDatatypeArity(handle());
  }

  private int getDatatypeArity(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_sort_dt_get_arity(pointer));
  }

  /* Tuple sort ---------------------------------------------------------- */

  /**
   * Get the length of a tuple sort.
   *
   * @return The length of a tuple sort.
   */
  public int getTupleLength()
  {
    return getTupleLength(handle());
  }

  private int getTupleLength(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_sort_tuple_get_length(pointer));
  }

  /**
   * Get the element sorts of a tuple sort.
   *
   * @return The element sorts of a tuple sort.
   */
  public Sort[] getTupleSorts()
  {
    MemorySegment[] pointers = getTupleSorts(handle());
    return Utils.getSorts(ctx, pointers);
  }

  private MemorySegment[] getTupleSorts(MemorySegment pointer)
  {
    return sortArray(pointer, CApi::cvc5_sort_tuple_get_element_sorts);
  }

  /**
   * Get the element sort of a nullable sort.
   *
   * @return The element sort of a nullable sort.
   */
  public Sort getNullableElementSort()
  {
    MemorySegment sortPointer = getNullableElementSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getNullableElementSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_sort_nullable_get_element_sort(pointer));
  }

  /**
   * Get the hash value of a sort.
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
    return Native.check(CApi.cvc5_sort_hash(pointer));
  }
}
