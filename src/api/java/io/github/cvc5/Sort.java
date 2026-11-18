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

import java.util.List;

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
    super(null, NULL_POINTER, null);
  }

  /** The native null object shared by all null sort instances. It is never freed. */
  private static final long NULL_POINTER = getNullSort();

  private static native long getNullSort();

  Sort(NativeContext ctx, long pointer)
  {
    super(ctx, pointer, Sort::deletePointer);
  }

  private static native void deletePointer(long pointer);

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
    if (this.pointer == sort.pointer)
    {
      return true;
    }
    return equals(getPointer(), sort.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

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
    return this.compareTo(getPointer(), s.getPointer());
  }

  private native int compareTo(long pointer1, long pointer2);

  /**
   * Get the kind of this sort.
   *
   * @return The kind of this sort.
   * @api.note This method is experimental and may change in future versions.
   * @throws CVC5ApiException on error
   */
  public SortKind getKind() throws CVC5ApiException
  {
    int value = getKind(getPointer());
    return SortKind.fromInt(value);
  }

  private native int getKind(long pointer);

  /**
   * Determine if the sort has a symbol.
   * @return True if the sort has a symbol.
   */
  public boolean hasSymbol()
  {
    return hasSymbol(getPointer());
  }

  private native boolean hasSymbol(long pointer);

  /**
   * Get the raw symbol of the symbol.
   *
   * @api.note Asserts hasSymbol().
   * @return The raw symbol of the symbol.
   */
  public String getSymbol()
  {
    return getSymbol(getPointer());
  }

  private native String getSymbol(long pointer);

  /**
   * Determine if this is the null sort.
   * @return True if this Sort is the null sort.
   */
  public boolean isNull()
  {
    return isNull(getPointer());
  }

  private native boolean isNull(long pointer);

  /**
   * Determine if this is the Boolean sort (SMT-LIB: {@code Bool}).
   * @return True if this sort is the Boolean sort.
   */
  public boolean isBoolean()
  {
    return isBoolean(getPointer());
  }

  private native boolean isBoolean(long pointer);

  /**
   * Determine if this is the integer sort (SMT-LIB: {@code Int}).
   * @return True if this sort is the integer sort.
   */
  public boolean isInteger()
  {
    return isInteger(getPointer());
  }

  private native boolean isInteger(long pointer);

  /**
   * Determine if this is the real sort (SMT-LIB: {@code Real}).
   * @return True if this sort is the real sort.
   */
  public boolean isReal()
  {
    return isReal(getPointer());
  }

  private native boolean isReal(long pointer);

  /**
   * Determine if this is the string sort (SMT-LIB: {@code String})..
   * @return True if this sort is the string sort.
   */
  public boolean isString()
  {
    return isString(getPointer());
  }

  private native boolean isString(long pointer);

  /**
   * Determine if this is the regular expression sort (SMT-LIB: {@code RegLan}).
   * @return True if this sort is the regular expression sort.
   */
  public boolean isRegExp()
  {
    return isRegExp(getPointer());
  }

  private native boolean isRegExp(long pointer);

  /**
   * Determine if this is the rounding mode sort (SMT-LIB: {@code RoundingMode}).
   * @return True if this sort is the rounding mode sort.
   */
  public boolean isRoundingMode()
  {
    return isRoundingMode(getPointer());
  }

  private native boolean isRoundingMode(long pointer);

  /**
   * Determine if this is a bit-vector sort (SMT-LIB: {@code (_ BitVec i)}).
   * @return True if this sort is a bit-vector sort.
   */
  public boolean isBitVector()
  {
    return isBitVector(getPointer());
  }

  private native boolean isBitVector(long pointer);

  /**
   * Determine if this is a finite field sort (SMT-LIB: {@code (_ FiniteField i)}).
   * @return True if this sort is a finite field sort.
   */
  public boolean isFiniteField()
  {
    return isFiniteField(getPointer());
  }

  private native boolean isFiniteField(long pointer);

  /**
   * Determine if this is a floatingpoint sort
   * (SMT-LIB: {@code (_ FloatingPoint eb sb)}).
   * @return True if this sort is a floating-point sort.
   */
  public boolean isFloatingPoint()
  {
    return isFloatingPoint(getPointer());
  }

  private native boolean isFloatingPoint(long pointer);

  /**
   * Determine if this is a datatype sort.
   * @return True if this sort is a datatype sort.
   */
  public boolean isDatatype()
  {
    return isDatatype(getPointer());
  }

  private native boolean isDatatype(long pointer);

  /**
   * Determine if this is a datatype constructor sort.
   * @return True if this sort is a datatype constructor sort.
   */
  public boolean isDatatypeConstructor()
  {
    return isDatatypeConstructor(getPointer());
  }

  private native boolean isDatatypeConstructor(long pointer);

  /**
   * Determine if this is a datatype selector sort.
   * @return True if this sort is a datatype selector sort.
   */
  public boolean isDatatypeSelector()
  {
    return isDatatypeSelector(getPointer());
  }

  private native boolean isDatatypeSelector(long pointer);

  /**
   * Determine if this is a datatype tester sort.
   * @return True if this sort is a datatype tester sort.
   */
  public boolean isDatatypeTester()
  {
    return isDatatypeTester(getPointer());
  }

  private native boolean isDatatypeTester(long pointer);

  /**
   * Determine if this is a datatype updater sort.
   * @return True if this sort is a datatype updater sort.
   */
  public boolean isDatatypeUpdater()
  {
    return isDatatypeUpdater(getPointer());
  }

  private native boolean isDatatypeUpdater(long pointer);

  /**
   * Determine if this is a function sort.
   * @return True if this sort is a function sort.
   */
  public boolean isFunction()
  {
    return isFunction(getPointer());
  }

  private native boolean isFunction(long pointer);

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
    return isPredicate(getPointer());
  }

  private native boolean isPredicate(long pointer);

  /**
   * Determine if this a tuple sort.
   * @return True if this sort is a tuple sort.
   */
  public boolean isTuple()
  {
    return isTuple(getPointer());
  }

  private native boolean isTuple(long pointer);

  /**
   * Determine if this a nullable sort.
   * @return True if this sort is a nullable sort.
   */
  public boolean isNullable()
  {
    return isNullable(getPointer());
  }

  private native boolean isNullable(long pointer);

  /**
   * Determine if this is a record sort.
   * @api.note This method is experimental and may change in future versions.
   * @return True if the sort is a record sort.
   */
  public boolean isRecord()
  {
    return isRecord(getPointer());
  }

  private native boolean isRecord(long pointer);

  /**
   * Determine if this is an array sort.
   * @return True if the sort is an array sort.
   */
  public boolean isArray()
  {
    return isArray(getPointer());
  }

  private native boolean isArray(long pointer);

  /**
   * Determine if this is a Set sort.
   * @return True if the sort is a Set sort.
   */
  public boolean isSet()
  {
    return isSet(getPointer());
  }

  private native boolean isSet(long pointer);

  /**
   * Determine if this is a Bag sort.
   * @return True if the sort is a Bag sort.
   */
  public boolean isBag()
  {
    return isBag(getPointer());
  }

  private native boolean isBag(long pointer);

  /**
   * Determine if this is a Sequence sort.
   * @return True if the sort is a Sequence sort.
   */
  public boolean isSequence()
  {
    return isSequence(getPointer());
  }

  private native boolean isSequence(long pointer);

  /**
   * Determine if this is an abstract sort.
   * @return True if the sort is a abstract sort.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public boolean isAbstract()
  {
    return isAbstract(getPointer());
  }

  private native boolean isAbstract(long pointer);

  /**
   * Determine if this is an uninterpreted sort.
   * @return True if this is an uninterpreted sort.
   */
  public boolean isUninterpretedSort()
  {
    return isUninterpretedSort(getPointer());
  }

  private native boolean isUninterpretedSort(long pointer);

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
    return isUninterpretedSortConstructor(getPointer());
  }

  private native boolean isUninterpretedSortConstructor(long pointer);

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
    return isInstantiated(getPointer());
  }

  private native boolean isInstantiated(long pointer);

  /**
   * Get the associated uninterpreted sort constructor of an instantiated
   * uninterpreted sort.
   *
   * @return The uninterpreted sort constructor sort.
   */
  public Sort getUninterpretedSortConstructor()
  {
    long sortPointer = getUninterpretedSortConstructor(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getUninterpretedSortConstructor(long pointer);

  /**
   * Get the underlying datatype of a datatype sort.
   *
   * @return The underlying datatype of a datatype sort.
   */
  public Datatype getDatatype()
  {
    long datatypePointer = getDatatype(getPointer());
    return new Datatype(ctx, datatypePointer);
  }

  private native long getDatatype(long pointer);

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
    long[] paramsPointers = Utils.getPointers(params);
    long sortPointer = instantiate(getPointer(), paramsPointers);
    return new Sort(ctx, sortPointer);
  }

  private native long instantiate(long pointer, long[] paramsPointers);

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
    long[] pointers = getInstantiatedParameters(getPointer());
    return Utils.getSorts(ctx, pointers);
  }

  private native long[] getInstantiatedParameters(long pointer);

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
    long sortPointer = substitute(getPointer(), sort.getPointer(), replacement.getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long substitute(long pointer, long sortPointer, long replacementPointer);

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
    long[] sortPointers = Utils.getPointers(sorts);
    long[] replacementPointers = Utils.getPointers(sorts);
    long sortPointer = substitute(getPointer(), sortPointers, replacementPointers);
    return new Sort(ctx, sortPointer);
  }

  private native long substitute(long pointer, long[] sortPointers, long[] replacementPointers);

  /**
   * @return A string representation of this sort.
   */
  protected native String toString(long pointer);

  /* Constructor sort ------------------------------------------------------- */

  /**
   * Get the arity of a datatype constructor sort.
   *
   * @return The arity of a datatype constructor sort.
   */
  public int getDatatypeConstructorArity()
  {
    return getDatatypeConstructorArity(getPointer());
  }

  private native int getDatatypeConstructorArity(long pointer);

  /**
   * Get the domain sorts of a datatype constructor sort.
   *
   * @return The domain sorts of a datatype constructor sort.
   */
  public Sort[] getDatatypeConstructorDomainSorts()
  {
    long[] pointers = getDatatypeConstructorDomainSorts(getPointer());
    return Utils.getSorts(ctx, pointers);
  }

  private native long[] getDatatypeConstructorDomainSorts(long pointer);

  /**
   * Get the codomain sort of a datatype constructor sort.
   *
   * @return The codomain sort of a datatype constructor sort.
   */
  public Sort getDatatypeConstructorCodomainSort()
  {
    long sortPointer = getDatatypeConstructorCodomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getDatatypeConstructorCodomainSort(long pointer);

  /* Selector sort ------------------------------------------------------- */

  /**
   * Get the domain sort of a datatype selector sort.
   * @return The domain sort of a datatype selector sort.
   */
  public Sort getDatatypeSelectorDomainSort()
  {
    long sortPointer = getDatatypeSelectorDomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getDatatypeSelectorDomainSort(long pointer);

  /**
   * Get the codomain sort of a datatype selector sort.
   *
   * @return The codomain sort of a datatype selector sort.
   */
  public Sort getDatatypeSelectorCodomainSort()
  {
    long sortPointer = getDatatypeSelectorCodomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getDatatypeSelectorCodomainSort(long pointer);

  /* Tester sort ------------------------------------------------------- */

  /**
   * Get the domain sort of a datatype tester sort.
   *
   * @return The domain sort of a datatype tester sort.
   */
  public Sort getDatatypeTesterDomainSort()
  {
    long sortPointer = getDatatypeTesterDomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getDatatypeTesterDomainSort(long pointer);

  /**
   * Get the codomain sort of a datatype tester sort, which is the Boolean sort.
   *
   * @return The codomain sort of a datatype tester sort, which is the Boolean
   *         sort.
   */
  public Sort getDatatypeTesterCodomainSort()
  {
    long sortPointer = getDatatypeTesterCodomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getDatatypeTesterCodomainSort(long pointer);

  /* Function sort ------------------------------------------------------- */

  /**
   * Get the arity of a function sort.
   *
   * @return The arity of a function sort.
   */
  public int getFunctionArity()
  {
    return getFunctionArity(getPointer());
  }

  private native int getFunctionArity(long pointer);

  /**
   * Get the domain sorts of a function sort.
   *
   * @return The domain sorts of a function sort.
   */
  public Sort[] getFunctionDomainSorts()
  {
    long[] pointers = getFunctionDomainSorts(getPointer());
    return Utils.getSorts(ctx, pointers);
  }

  private native long[] getFunctionDomainSorts(long pointer);

  /**
   * Get the codomain sort of a function sort.
   *
   * @return The codomain sort of a function sort.
   */
  public Sort getFunctionCodomainSort()
  {
    long sortPointer = getFunctionCodomainSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getFunctionCodomainSort(long pointer);

  /* Array sort ---------------------------------------------------------- */

  /**
   * Get the array index sort of an array sort.
   * @return The array index sort of an array sort.
   */
  public Sort getArrayIndexSort()
  {
    long sortPointer = getArrayIndexSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getArrayIndexSort(long pointer);

  /**
   * Get the array element sort of an array element sort.
   *
   * @return The array element sort of an array element sort.
   */
  public Sort getArrayElementSort()
  {
    long sortPointer = getArrayElementSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getArrayElementSort(long pointer);

  /* Set sort ------------------------------------------------------------ */

  /**
   * Get the element sort of a set sort.
   *
   * @return The element sort of a set sort.
   */
  public Sort getSetElementSort()
  {
    long sortPointer = getSetElementSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getSetElementSort(long pointer);

  /* Bag sort ------------------------------------------------------------ */

  /**
   * Get the element sort of a bag sort.
   *
   * @return The element sort of a bag sort.
   */
  public Sort getBagElementSort()
  {
    long sortPointer = getBagElementSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getBagElementSort(long pointer);

  /* Sequence sort ------------------------------------------------------- */

  /**
   * Get the element sort of a sequence sort.
   *
   * @return The element sort of a sequence sort.
   */
  public Sort getSequenceElementSort()
  {
    long sortPointer = getSequenceElementSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getSequenceElementSort(long pointer);

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
    int value = getAbstractedKind(getPointer());
    return SortKind.fromInt(value);
  }

  private native int getAbstractedKind(long pointer);

  /* Sort constructor sort ----------------------------------------------- */

  /**
   * Get the arity of an uninterpreted sort constructor sort.
   *
   * @return The arity of an uninterpreted sort constructor sort.
   */
  public int getUninterpretedSortConstructorArity()
  {
    return getUninterpretedSortConstructorArity(getPointer());
  }

  private native int getUninterpretedSortConstructorArity(long pointer);

  /* Bit-vector sort ----------------------------------------------------- */

  /**
   * Get the bit-width of the bit-vector sort.
   *
   * @return The bit-width of the bit-vector sort.
   */
  public int getBitVectorSize()
  {
    return getBitVectorSize(getPointer());
  }

  private native int getBitVectorSize(long pointer);

  /* Finite field sort --------------------------------------------------- */

  /**
   * Get the bit-width of the bit-vector sort.
   *
   * @return The bit-width of the bit-vector sort.
   */
  public String getFiniteFieldSize()
  {
    return getFiniteFieldSize(getPointer());
  }

  private native String getFiniteFieldSize(long pointer);

  /* Floating-point sort ------------------------------------------------- */

  /**
   * Get the bit-width of the exponent of the floating-point sort.
   *
   * @return The bit-width of the exponent of the floating-point sort.
   */
  public int getFloatingPointExponentSize()
  {
    return getFloatingPointExponentSize(getPointer());
  }

  private native int getFloatingPointExponentSize(long pointer);

  /**
   * Get the width of the significand of the floating-point sort.
   *
   * @return The width of the significand of the floating-point sort.
   */
  public int getFloatingPointSignificandSize()
  {
    return getFloatingPointSignificandSize(getPointer());
  }

  private native int getFloatingPointSignificandSize(long pointer);

  /* Datatype sort ------------------------------------------------------- */

  /**
   * Get the arity of a datatype sort.
   *
   * @return The arity of a datatype sort.
   */
  public int getDatatypeArity()
  {
    return getDatatypeArity(getPointer());
  }

  private native int getDatatypeArity(long pointer);

  /* Tuple sort ---------------------------------------------------------- */

  /**
   * Get the length of a tuple sort.
   *
   * @return The length of a tuple sort.
   */
  public int getTupleLength()
  {
    return getTupleLength(getPointer());
  }

  private native int getTupleLength(long pointer);

  /**
   * Get the element sorts of a tuple sort.
   *
   * @return The element sorts of a tuple sort.
   */
  public Sort[] getTupleSorts()
  {
    long[] pointers = getTupleSorts(getPointer());
    return Utils.getSorts(ctx, pointers);
  }

  private native long[] getTupleSorts(long pointer);

  /**
   * Get the element sort of a nullable sort.
   *
   * @return The element sort of a nullable sort.
   */
  public Sort getNullableElementSort()
  {
    long sortPointer = getNullableElementSort(getPointer());
    return new Sort(ctx, sortPointer);
  }

  private native long getNullableElementSort(long pointer);

  /**
   * Get the hash value of a sort.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(getPointer()));
  }

  private native long hashCode(long pointer);
}
