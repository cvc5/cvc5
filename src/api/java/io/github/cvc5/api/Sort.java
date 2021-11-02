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

import java.util.List;

public class Sort extends AbstractPointer implements Comparable<Sort>
{
  // region construction and destruction
  Sort(Solver solver, long pointer)
  {
    super(solver, pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  // endregion

  /**
   * Comparison for structural equality.
   * @param s the sort to compare to
   * @return true if the sorts are equal
   */
  @Override public boolean equals(Object s)
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
   * @param s the sort to compare to
   * @return a negative integer, zero, or a positive integer as this sort
   * is less than, equal to, or greater than the specified sort.
   */
  @Override public int compareTo(Sort s)
  {
    return this.compareTo(pointer, s.getPointer());
  }

  private native int compareTo(long pointer1, long pointer2);

  /**
   * @return true if this Sort is a null sort.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Is this a Boolean sort?
   * @return true if the sort is a Boolean sort
   */
  public boolean isBoolean()
  {
    return isBoolean(pointer);
  }

  private native boolean isBoolean(long pointer);

  /**
   * Is this a integer sort?
   * @return true if the sort is a integer sort
   */
  public boolean isInteger()
  {
    return isInteger(pointer);
  }

  private native boolean isInteger(long pointer);

  /**
   * Is this a real sort?
   * @return true if the sort is a real sort
   */
  public boolean isReal()
  {
    return isReal(pointer);
  }

  private native boolean isReal(long pointer);

  /**
   * Is this a string sort?
   * @return true if the sort is the string sort
   */
  public boolean isString()
  {
    return isString(pointer);
  }

  private native boolean isString(long pointer);

  /**
   * Is this a regexp sort?
   * @return true if the sort is the regexp sort
   */
  public boolean isRegExp()
  {
    return isRegExp(pointer);
  }

  private native boolean isRegExp(long pointer);

  /**
   * Is this a rounding mode sort?
   * @return true if the sort is the rounding mode sort
   */
  public boolean isRoundingMode()
  {
    return isRoundingMode(pointer);
  }

  private native boolean isRoundingMode(long pointer);

  /**
   * Is this a bit-vector sort?
   * @return true if the sort is a bit-vector sort
   */
  public boolean isBitVector()
  {
    return isBitVector(pointer);
  }

  private native boolean isBitVector(long pointer);

  /**
   * Is this a floating-point sort?
   * @return true if the sort is a floating-point sort
   */
  public boolean isFloatingPoint()
  {
    return isFloatingPoint(pointer);
  }

  private native boolean isFloatingPoint(long pointer);

  /**
   * Is this a datatype sort?
   * @return true if the sort is a datatype sort
   */
  public boolean isDatatype()
  {
    return isDatatype(pointer);
  }

  private native boolean isDatatype(long pointer);

  /**
   * Is this a parametric datatype sort?
   * @return true if the sort is a parametric datatype sort
   */
  public boolean isParametricDatatype()
  {
    return isParametricDatatype(pointer);
  }

  private native boolean isParametricDatatype(long pointer);

  /**
   * Is this a constructor sort?
   * @return true if the sort is a constructor sort
   */
  public boolean isConstructor()
  {
    return isConstructor(pointer);
  }

  private native boolean isConstructor(long pointer);

  /**
   * Is this a selector sort?
   * @return true if the sort is a selector sort
   */
  public boolean isSelector()
  {
    return isSelector(pointer);
  }

  private native boolean isSelector(long pointer);

  /**
   * Is this a tester sort?
   * @return true if the sort is a tester sort
   */
  public boolean isTester()
  {
    return isTester(pointer);
  }

  private native boolean isTester(long pointer);

  /**
   * Is this a datatype updater sort?
   * @return true if the sort is a datatype updater sort
   */
  public boolean isUpdater()
  {
    return isUpdater(pointer);
  }

  private native boolean isUpdater(long pointer);

  /**
   * Is this a function sort?
   * @return true if the sort is a function sort
   */
  public boolean isFunction()
  {
    return isFunction(pointer);
  }

  private native boolean isFunction(long pointer);

  /**
   * Is this a predicate sort?
   * That is, is this a function sort mapping to Boolean? All predicate
   * sorts are also function sorts.
   * @return true if the sort is a predicate sort
   */
  public boolean isPredicate()
  {
    return isPredicate(pointer);
  }

  private native boolean isPredicate(long pointer);

  /**
   * Is this a tuple sort?
   * @return true if the sort is a tuple sort
   */
  public boolean isTuple()
  {
    return isTuple(pointer);
  }

  private native boolean isTuple(long pointer);

  /**
   * Is this a record sort?
   * @return true if the sort is a record sort
   */
  public boolean isRecord()
  {
    return isRecord(pointer);
  }

  private native boolean isRecord(long pointer);

  /**
   * Is this an array sort?
   * @return true if the sort is a array sort
   */
  public boolean isArray()
  {
    return isArray(pointer);
  }

  private native boolean isArray(long pointer);

  /**
   * Is this a Set sort?
   * @return true if the sort is a Set sort
   */
  public boolean isSet()
  {
    return isSet(pointer);
  }

  private native boolean isSet(long pointer);

  /**
   * Is this a Bag sort?
   * @return true if the sort is a Bag sort
   */
  public boolean isBag()
  {
    return isBag(pointer);
  }

  private native boolean isBag(long pointer);

  /**
   * Is this a Sequence sort?
   * @return true if the sort is a Sequence sort
   */
  public boolean isSequence()
  {
    return isSequence(pointer);
  }

  private native boolean isSequence(long pointer);

  /**
   * Is this a sort kind?
   * @return true if this is a sort kind
   */
  public boolean isUninterpretedSort()
  {
    return isUninterpretedSort(pointer);
  }

  private native boolean isUninterpretedSort(long pointer);

  /**
   * Is this a sort constructor kind?
   * @return true if this is a sort constructor kind
   */
  public boolean isSortConstructor()
  {
    return isSortConstructor(pointer);
  }

  private native boolean isSortConstructor(long pointer);

  /**
   * Is this a first-class sort?
   * First-class sorts are sorts for which:
   * (1) we handle equalities between terms of that type, and
   * (2) they are allowed to be parameters of parametric sorts (e.g. index or
   *     element sorts of arrays).
   *
   * Examples of sorts that are not first-class include sort constructor sorts
   * and regular expression sorts.
   *
   * @return true if this is a first-class sort
   */
  public boolean isFirstClass()
  {
    return isFirstClass(pointer);
  }

  private native boolean isFirstClass(long pointer);

  /**
   * Is this a function-LIKE sort?
   *
   * Anything function-like except arrays (e.g., datatype selectors) is
   * considered a function here. Function-like terms can not be the argument
   * or return value for any term that is function-like.
   * This is mainly to avoid higher order.
   *
   * Note that arrays are explicitly not considered function-like here.
   *
   * @return true if this is a function-like sort
   */
  public boolean isFunctionLike()
  {
    return isFunctionLike(pointer);
  }

  private native boolean isFunctionLike(long pointer);

  /**
   * Is this sort a subsort of the given sort?
   * @return true if this sort is a subsort of s
   */
  public boolean isSubsortOf(Sort s)
  {
    return isSubsortOf(pointer, s.getPointer());
  }

  private native boolean isSubsortOf(long pointer, long sortPointer);

  /**
   * Is this sort comparable to the given sort (i.e., do they share
   * a common ancestor in the subsort tree)?
   * @return true if this sort is comparable to s
   */
  public boolean isComparableTo(Sort s)
  {
    return isComparableTo(pointer, s.getPointer());
  }

  private native boolean isComparableTo(long pointer, long sortPointer);

  /**
   * @return the underlying datatype of a datatype sort
   */
  public Datatype getDatatype()
  {
    long datatypePointer = getDatatype(pointer);
    return new Datatype(solver, datatypePointer);
  }

  private native long getDatatype(long pointer);

  /**
   * Instantiate a parameterized datatype/sort sort.
   * Create sorts parameter with Solver.mkParamSort().
   * @param params the list of sort parameters to instantiate with
   */
  public Sort instantiate(List<Sort> params)
  {
    return instantiate(params.toArray(new Sort[0]));
  }

  /**
   * Instantiate a parameterized datatype/sort sort.
   * Create sorts parameter with Solver.mkParamSort().
   * @param params the list of sort parameters to instantiate with
   */
  public Sort instantiate(Sort[] params)
  {
    long[] paramsPointers = Utils.getPointers(params);
    long sortPointer = instantiate(pointer, paramsPointers);
    return new Sort(solver, sortPointer);
  }

  private native long instantiate(long pointer, long[] paramsPointers);

  /**
   * Substitution of Sorts.
   * @param sort the subsort to be substituted within this sort.
   * @param replacement the sort replacing the substituted subsort.
   */
  public Sort substitute(Sort sort, Sort replacement)
  {
    long sortPointer = substitute(pointer, sort.getPointer(), replacement.getPointer());
    return new Sort(solver, sortPointer);
  }

  private native long substitute(long pointer, long sortPointer, long replacementPointer);

  /**
   * Simultaneous substitution of Sorts.
   * @param sorts the subsorts to be substituted within this sort.
   * @param replacements the sort replacing the substituted subsorts.
   */
  public Sort substitute(Sort[] sorts, Sort[] replacements)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long[] replacementPointers = Utils.getPointers(sorts);
    long sortPointer = substitute(pointer, sortPointers, replacementPointers);
    return new Sort(solver, sortPointer);
  }

  private native long substitute(long pointer, long[] sortPointers, long[] replacementPointers);

  /**
   * Output a string representation of this sort to a given stream.
   * @param out the output stream
   */
  // TODO: do we need to support this?
  // void toStream(std::ostream& out)

  /**
   * @return a string representation of this sort
   */
  protected native String toString(long pointer);

  /* Constructor sort ------------------------------------------------------- */

  /**
   * @return the arity of a constructor sort
   */
  public int getConstructorArity()
  {
    return getConstructorArity(pointer);
  }

  private native int getConstructorArity(long pointer);

  /**
   * @return the domain sorts of a constructor sort
   */
  public Sort[] getConstructorDomainSorts()
  {
    long[] pointers = getConstructorDomainSorts(pointer);
    return Utils.getSorts(solver, pointers);
  }

  private native long[] getConstructorDomainSorts(long pointer);

  /**
   * @return the codomain sort of a constructor sort
   */
  public Sort getConstructorCodomainSort()
  {
    long sortPointer = getConstructorCodomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getConstructorCodomainSort(long pointer);

  /* Selector sort ------------------------------------------------------- */

  /**
   * @return the domain sort of a selector sort
   */
  public Sort getSelectorDomainSort()
  {
    long sortPointer = getSelectorDomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getSelectorDomainSort(long pointer);

  /**
   * @return the codomain sort of a selector sort
   */
  public Sort getSelectorCodomainSort()
  {
    long sortPointer = getSelectorCodomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getSelectorCodomainSort(long pointer);

  /* Tester sort ------------------------------------------------------- */

  /**
   * @return the domain sort of a tester sort
   */
  public Sort getTesterDomainSort()
  {
    long sortPointer = getTesterDomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getTesterDomainSort(long pointer);

  /**
   * @return the codomain sort of a tester sort, which is the Boolean sort
   */
  public Sort getTesterCodomainSort()
  {
    long sortPointer = getTesterCodomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getTesterCodomainSort(long pointer);

  /* Function sort ------------------------------------------------------- */

  /**
   * @return the arity of a function sort
   */
  public int getFunctionArity()
  {
    return getFunctionArity(pointer);
  }

  private native int getFunctionArity(long pointer);

  /**
   * @return the domain sorts of a function sort
   */
  public Sort[] getFunctionDomainSorts()
  {
    long[] pointers = getFunctionDomainSorts(pointer);
    return Utils.getSorts(solver, pointers);
  }

  private native long[] getFunctionDomainSorts(long pointer);

  /**
   * @return the codomain sort of a function sort
   */
  public Sort getFunctionCodomainSort()
  {
    long sortPointer = getFunctionCodomainSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getFunctionCodomainSort(long pointer);

  /* Array sort ---------------------------------------------------------- */

  /**
   * @return the array index sort of an array sort
   */
  public Sort getArrayIndexSort()
  {
    long sortPointer = getArrayIndexSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getArrayIndexSort(long pointer);

  /**
   * @return the array element sort of an array element sort
   */
  public Sort getArrayElementSort()
  {
    long sortPointer = getArrayElementSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getArrayElementSort(long pointer);

  /* Set sort ------------------------------------------------------------ */

  /**
   * @return the element sort of a set sort
   */
  public Sort getSetElementSort()
  {
    long sortPointer = getSetElementSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getSetElementSort(long pointer);

  /* Bag sort ------------------------------------------------------------ */

  /**
   * @return the element sort of a bag sort
   */
  public Sort getBagElementSort()
  {
    long sortPointer = getBagElementSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getBagElementSort(long pointer);

  /* Sequence sort ------------------------------------------------------- */

  /**
   * @return the element sort of a sequence sort
   */
  public Sort getSequenceElementSort()
  {
    long sortPointer = getSequenceElementSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getSequenceElementSort(long pointer);

  /* Uninterpreted sort -------------------------------------------------- */

  /**
   * @return the name of an uninterpreted sort
   */
  public String getUninterpretedSortName()
  {
    return getUninterpretedSortName(pointer);
  }

  private native String getUninterpretedSortName(long pointer);

  /**
   * @return true if an uninterpreted sort is parameterezied
   */
  public boolean isUninterpretedSortParameterized()
  {
    return isUninterpretedSortParameterized(pointer);
  }

  private native boolean isUninterpretedSortParameterized(long pointer);

  /**
   * @return the parameter sorts of an uninterpreted sort
   */
  public Sort[] getUninterpretedSortParamSorts()
  {
    long[] pointers = getUninterpretedSortParamSorts(pointer);
    return Utils.getSorts(solver, pointers);
  }

  private native long[] getUninterpretedSortParamSorts(long pointer);

  /* Sort constructor sort ----------------------------------------------- */

  /**
   * @return the name of a sort constructor sort
   */
  public String getSortConstructorName()
  {
    return getSortConstructorName(pointer);
  }

  private native String getSortConstructorName(long pointer);

  /**
   * @return the arity of a sort constructor sort
   */
  public int getSortConstructorArity()
  {
    return getSortConstructorArity(pointer);
  }

  private native int getSortConstructorArity(long pointer);

  /* Bit-vector sort ----------------------------------------------------- */

  /**
   * @return the bit-width of the bit-vector sort
   */
  public int getBitVectorSize()
  {
    return getBitVectorSize(pointer);
  }

  private native int getBitVectorSize(long pointer);

  /* Floating-point sort ------------------------------------------------- */

  /**
   * @return the bit-width of the exponent of the floating-point sort
   */
  public int getFloatingPointExponentSize()
  {
    return getFloatingPointExponentSize(pointer);
  }

  private native int getFloatingPointExponentSize(long pointer);

  /**
   * @return the width of the significand of the floating-point sort
   */
  public int getFloatingPointSignificandSize()
  {
    return getFloatingPointSignificandSize(pointer);
  }

  private native int getFloatingPointSignificandSize(long pointer);

  /* Datatype sort ------------------------------------------------------- */

  /**
   * @return the parameter sorts of a datatype sort
   */
  public Sort[] getDatatypeParamSorts()
  {
    long[] pointers = getDatatypeParamSorts(pointer);
    return Utils.getSorts(solver, pointers);
  }

  private native long[] getDatatypeParamSorts(long pointer);

  /**
   * @return the arity of a datatype sort
   */
  public int getDatatypeArity()
  {
    return getDatatypeArity(pointer);
  }

  private native int getDatatypeArity(long pointer);

  /* Tuple sort ---------------------------------------------------------- */

  /**
   * @return the length of a tuple sort
   */
  public int getTupleLength()
  {
    return getTupleLength(pointer);
  }

  private native int getTupleLength(long pointer);

  /**
   * @return the element sorts of a tuple sort
   */
  public Sort[] getTupleSorts()
  {
    long[] pointers = getTupleSorts(pointer);
    return Utils.getSorts(solver, pointers);
  }

  private native long[] getTupleSorts(long pointer);
}
