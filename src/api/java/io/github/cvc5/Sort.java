/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    super(getNullSort());
  }

  private static native long getNullSort();

  Sort(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
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
      return true;
    if (s == null || getClass() != s.getClass())
      return false;
    Sort sort = (Sort) s;
    if (this.pointer == sort.pointer)
    {
      return true;
    }
    return equals(pointer, sort.getPointer());
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
    return this.compareTo(pointer, s.getPointer());
  }

  private native int compareTo(long pointer1, long pointer2);

  /**
   * @return The kind of this sort.
   * @api.note This method is experimental and may change in future versions.
   * @throws CVC5ApiException
   */
  public SortKind getKind() throws CVC5ApiException
  {
    int value = getKind(pointer);
    return SortKind.fromInt(value);
  }

  private native int getKind(long pointer);

  /**
   * @return True if the sort has a symbol.
   */
  public boolean hasSymbol()
  {
    return hasSymbol(pointer);
  }

  private native boolean hasSymbol(long pointer);

  /**
   * @api.note Asserts hasSymbol().
   * @return The raw symbol of the symbol.
   */
  public String getSymbol()
  {
    return getSymbol(pointer);
  }

  private native String getSymbol(long pointer);

  /**
   * Determine if this is the null sort.
   * @return True if this Sort is the null sort.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Determine if this is the Boolean sort (SMT-LIB: {@code Bool}).
   * @return True if this sort is the Boolean sort.
   */
  public boolean isBoolean()
  {
    return isBoolean(pointer);
  }

  private native boolean isBoolean(long pointer);

  /**
   * Determine if this is the integer sort (SMT-LIB: {@code Int}).
   * @return True if this sort is the integer sort.
   */
  public boolean isInteger()
  {
    return isInteger(pointer);
  }

  private native boolean isInteger(long pointer);

  /**
   * Determine if this is the real sort (SMT-LIB: {@code Real}).
   * @return True if this sort is the real sort.
   */
  public boolean isReal()
  {
    return isReal(pointer);
  }

  private native boolean isReal(long pointer);

  /**
   * Determine if this is the string sort (SMT-LIB: {@code String})..
   * @return True if this sort is the string sort.
   */
  public boolean isString()
  {
    return isString(pointer);
  }

  private native boolean isString(long pointer);

  /**
   * Determine if this is the regular expression sort (SMT-LIB: {@code RegLan}).
   * @return True if this sort is the regular expression sort.
   */
  public boolean isRegExp()
  {
    return isRegExp(pointer);
  }

  private native boolean isRegExp(long pointer);

  /**
   * Determine if this is the rounding mode sort (SMT-LIB: {@code RoundingMode}).
   * @return True if this sort is the rounding mode sort.
   */
  public boolean isRoundingMode()
  {
    return isRoundingMode(pointer);
  }

  private native boolean isRoundingMode(long pointer);

  /**
   * Determine if this is a bit-vector sort (SMT-LIB: {@code (_ BitVec i)}).
   * @return True if this sort is a bit-vector sort.
   */
  public boolean isBitVector()
  {
    return isBitVector(pointer);
  }

  private native boolean isBitVector(long pointer);

  /**
   * Determine if this is a finite field sort (SMT-LIB: {@code (_ FiniteField i)}).
   * @return True if this sort is a finite field sort.
   */
  public boolean isFiniteField()
  {
    return isFiniteField(pointer);
  }

  private native boolean isFiniteField(long pointer);

  /**
   * Determine if this is a floatingpoint sort
   * (SMT-LIB: {@code (_ FloatingPoint eb sb)}).
   * @return True if this sort is a floating-point sort.
   */
  public boolean isFloatingPoint()
  {
    return isFloatingPoint(pointer);
  }

  private native boolean isFloatingPoint(long pointer);

  /**
   * Determine if this is a datatype sort.
   * @return True if this sort is a datatype sort.
   */
  public boolean isDatatype()
  {
    return isDatatype(pointer);
  }

  private native boolean isDatatype(long pointer);

  /**
   * Determine if this is a datatype constructor sort.
   * @return True if this sort is a datatype constructor sort.
   */
  public boolean isDatatypeConstructor()
  {
    return isDatatypeConstructor(pointer);
  }

  private native boolean isDatatypeConstructor(long pointer);

  /**
   * Determine if this is a datatype selector sort.
   * @return True if this sort is a datatype selector sort.
   */
  public boolean isDatatypeSelector()
  {
    return isDatatypeSelector(pointer);
  }

  private native boolean isDatatypeSelector(long pointer);

  /**
   * Determine if this is a datatype tester sort.
   * @return True if this sort is a datatype tester sort.
   */
  public boolean isDatatypeTester()
  {
    return isDatatypeTester(pointer);
  }

  private native boolean isDatatypeTester(long pointer);

  /**
   * Determine if this is a datatype updater sort.
   * @return True if this sort is a datatype updater sort.
   */
  public boolean isDatatypeUpdater()
  {
    return isDatatypeUpdater(pointer);
  }

  private native boolean isDatatypeUpdater(long pointer);

  /**
   * Determine if this is a function sort.
   * @return True if this sort is a function sort.
   */
  public boolean isFunction()
  {
    return isFunction(pointer);
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
    return isPredicate(pointer);
  }

  private native boolean isPredicate(long pointer);

  /**
   * Determine if this a tuple sort.
   * @return True if this sort is a tuple sort.
   */
  public boolean isTuple()
  {
    return isTuple(pointer);
  }

  private native boolean isTuple(long pointer);

  /**
   * Determine if this is a record sort.
   * @api.note This method is experimental and may change in future versions.
   * @return True if the sort is a record sort.
   */
  public boolean isRecord()
  {
    return isRecord(pointer);
  }

  private native boolean isRecord(long pointer);

  /**
   * Determine if this is an array sort.
   * @return True if the sort is an array sort.
   */
  public boolean isArray()
  {
    return isArray(pointer);
  }

  private native boolean isArray(long pointer);

  /**
   * Determine if this is a Set sort.
   * @return True if the sort is a Set sort.
   */
  public boolean isSet()
  {
    return isSet(pointer);
  }

  private native boolean isSet(long pointer);

  /**
   * Determine if this is a Bag sort.
   * @return True if the sort is a Bag sort.
   */
  public boolean isBag()
  {
    return isBag(pointer);
  }

  private native boolean isBag(long pointer);

  /**
   * Determine if this is a Sequence sort.
   * @return True if the sort is a Sequence sort.
   */
  public boolean isSequence()
  {
    return isSequence(pointer);
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
    return isAbstract(pointer);
  }

  private native boolean isAbstract(long pointer);

  /**
   * Determine if this is an uninterpreted sort.
   * @return True if this is an uninterpreted sort.
   */
  public boolean isUninterpretedSort()
  {
    return isUninterpretedSort(pointer);
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
    return isUninterpretedSortConstructor(pointer);
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
    return isInstantiated(pointer);
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
    long sortPointer = getUninterpretedSortConstructor(pointer);
    return new Sort(sortPointer);
  }

  private native long getUninterpretedSortConstructor(long pointer);

  /**
   * @return The underlying datatype of a datatype sort.
   */
  public Datatype getDatatype()
  {
    long datatypePointer = getDatatype(pointer);
    return new Datatype(datatypePointer);
  }

  private native long getDatatype(long pointer);

  /**
   * Instantiate a parameterized datatype sort or uninterpreted sort
   * constructor sort.
   *
   * Create sorts parameter with {@link Solver#mkParamSort(String)}).
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param params The list of sort parameters to instantiate with.
   */
  public Sort instantiate(Sort[] params)
  {
    long[] paramsPointers = Utils.getPointers(params);
    long sortPointer = instantiate(pointer, paramsPointers);
    return new Sort(sortPointer);
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
    long[] pointers = getInstantiatedParameters(pointer);
    return Utils.getSorts(pointers);
  }

  private native long[] getInstantiatedParameters(long pointer);

  /**
   * Substitution of Sorts.
   *
   * Note that this replacement is applied during a pre-order traversal and
   * only once to the sort. It is not run until fix point.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sort The subsort to be substituted within this sort.
   * @param replacement The sort replacing the substituted subsort.
   */
  public Sort substitute(Sort sort, Sort replacement)
  {
    long sortPointer = substitute(pointer, sort.getPointer(), replacement.getPointer());
    return new Sort(sortPointer);
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
   */
  public Sort substitute(Sort[] sorts, Sort[] replacements)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long[] replacementPointers = Utils.getPointers(sorts);
    long sortPointer = substitute(pointer, sortPointers, replacementPointers);
    return new Sort(sortPointer);
  }

  private native long substitute(long pointer, long[] sortPointers, long[] replacementPointers);

  /**
   * @return A string representation of this sort.
   */
  protected native String toString(long pointer);

  /* Constructor sort ------------------------------------------------------- */

  /**
   * @return The arity of a datatype constructor sort.
   */
  public int getDatatypeConstructorArity()
  {
    return getDatatypeConstructorArity(pointer);
  }

  private native int getDatatypeConstructorArity(long pointer);

  /**
   * @return The domain sorts of a datatype constructor sort.
   */
  public Sort[] getDatatypeConstructorDomainSorts()
  {
    long[] pointers = getDatatypeConstructorDomainSorts(pointer);
    return Utils.getSorts(pointers);
  }

  private native long[] getDatatypeConstructorDomainSorts(long pointer);

  /**
   * @return The codomain sort of a datatype constructor sort.
   */
  public Sort getDatatypeConstructorCodomainSort()
  {
    long sortPointer = getDatatypeConstructorCodomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getDatatypeConstructorCodomainSort(long pointer);

  /* Selector sort ------------------------------------------------------- */

  /**
   * @return The domain sort of a datatype selector sort.
   */
  public Sort getDatatypeSelectorDomainSort()
  {
    long sortPointer = getDatatypeSelectorDomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getDatatypeSelectorDomainSort(long pointer);

  /**
   * @return The codomain sort of a datatype selector sort.
   */
  public Sort getDatatypeSelectorCodomainSort()
  {
    long sortPointer = getDatatypeSelectorCodomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getDatatypeSelectorCodomainSort(long pointer);

  /* Tester sort ------------------------------------------------------- */

  /**
   * @return The domain sort of a datatype tester sort.
   */
  public Sort getDatatypeTesterDomainSort()
  {
    long sortPointer = getDatatypeTesterDomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getDatatypeTesterDomainSort(long pointer);

  /**
   * @return The codomain sort of a datatype tester sort, which is the Boolean
   *         sort.
   */
  public Sort getDatatypeTesterCodomainSort()
  {
    long sortPointer = getDatatypeTesterCodomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getDatatypeTesterCodomainSort(long pointer);

  /* Function sort ------------------------------------------------------- */

  /**
   * @return The arity of a function sort.
   */
  public int getFunctionArity()
  {
    return getFunctionArity(pointer);
  }

  private native int getFunctionArity(long pointer);

  /**
   * @return The domain sorts of a function sort.
   */
  public Sort[] getFunctionDomainSorts()
  {
    long[] pointers = getFunctionDomainSorts(pointer);
    return Utils.getSorts(pointers);
  }

  private native long[] getFunctionDomainSorts(long pointer);

  /**
   * @return The codomain sort of a function sort.
   */
  public Sort getFunctionCodomainSort()
  {
    long sortPointer = getFunctionCodomainSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getFunctionCodomainSort(long pointer);

  /* Array sort ---------------------------------------------------------- */

  /**
   * @return The array index sort of an array sort.
   */
  public Sort getArrayIndexSort()
  {
    long sortPointer = getArrayIndexSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getArrayIndexSort(long pointer);

  /**
   * @return The array element sort of an array element sort.
   */
  public Sort getArrayElementSort()
  {
    long sortPointer = getArrayElementSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getArrayElementSort(long pointer);

  /* Set sort ------------------------------------------------------------ */

  /**
   * @return The element sort of a set sort.
   */
  public Sort getSetElementSort()
  {
    long sortPointer = getSetElementSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getSetElementSort(long pointer);

  /* Bag sort ------------------------------------------------------------ */

  /**
   * @return The element sort of a bag sort.
   */
  public Sort getBagElementSort()
  {
    long sortPointer = getBagElementSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getBagElementSort(long pointer);

  /* Sequence sort ------------------------------------------------------- */

  /**
   * @return The element sort of a sequence sort.
   */
  public Sort getSequenceElementSort()
  {
    long sortPointer = getSequenceElementSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getSequenceElementSort(long pointer);

  /* Abstract sort ------------------------------------------------------- */

  /**
   * @return The sort kind of an abstract sort, which denotes the kind of
   * sorts that this abstract sort denotes.
   * @throws CVC5ApiException
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public SortKind getAbstractedKind() throws CVC5ApiException
  {
    int value = getAbstractedKind(pointer);
    return SortKind.fromInt(value);
  }

  private native int getAbstractedKind(long pointer);

  /* Sort constructor sort ----------------------------------------------- */

  /**
   * @return The arity of an uninterpreted sort constructor sort.
   */
  public int getUninterpretedSortConstructorArity()
  {
    return getUninterpretedSortConstructorArity(pointer);
  }

  private native int getUninterpretedSortConstructorArity(long pointer);

  /* Bit-vector sort ----------------------------------------------------- */

  /**
   * @return The bit-width of the bit-vector sort.
   */
  public int getBitVectorSize()
  {
    return getBitVectorSize(pointer);
  }

  private native int getBitVectorSize(long pointer);

  /* Finite field sort --------------------------------------------------- */

  /**
   * @return The bit-width of the bit-vector sort.
   */
  public String getFiniteFieldSize()
  {
    return getFiniteFieldSize(pointer);
  }

  private native String getFiniteFieldSize(long pointer);

  /* Floating-point sort ------------------------------------------------- */

  /**
   * @return The bit-width of the exponent of the floating-point sort.
   */
  public int getFloatingPointExponentSize()
  {
    return getFloatingPointExponentSize(pointer);
  }

  private native int getFloatingPointExponentSize(long pointer);

  /**
   * @return The width of the significand of the floating-point sort.
   */
  public int getFloatingPointSignificandSize()
  {
    return getFloatingPointSignificandSize(pointer);
  }

  private native int getFloatingPointSignificandSize(long pointer);

  /* Datatype sort ------------------------------------------------------- */

  /**
   * @return The arity of a datatype sort.
   */
  public int getDatatypeArity()
  {
    return getDatatypeArity(pointer);
  }

  private native int getDatatypeArity(long pointer);

  /* Tuple sort ---------------------------------------------------------- */

  /**
   * @return The length of a tuple sort.
   */
  public int getTupleLength()
  {
    return getTupleLength(pointer);
  }

  private native int getTupleLength(long pointer);

  /**
   * @return The element sorts of a tuple sort.
   */
  public Sort[] getTupleSorts()
  {
    long[] pointers = getTupleSorts(pointer);
    return Utils.getSorts(pointers);
  }

  private native long[] getTupleSorts(long pointer);
}
