/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 java API.
 */

package io.github.cvc5;

import java.io.IOException;
import java.util.*;

/**
 * A cvc5 term manager.
 */
public class TermManager extends AbstractPointer
{
  static
  {
    Utils.loadLibraries();
  }

  private static native long newTermManager();

  protected native void deletePointer(long pointer);

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
    super(TermManager.newTermManager());
  }

  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package
   * @param pointer The cpp pointer to TermManager
   */
  TermManager(long tmPointer)
  {
    super(tmPointer);
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
    TermManager tm = (TermManager) o;
    if (this.pointer == tm.pointer)
    {
      return true;
    }
    return false;
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
    long statisticsPointer = getStatistics(pointer);
    return new Statistics(statisticsPointer);
  }

  private native long getStatistics(long pointer);

  /* .................................................................... */
  /* Sorts Handling                                                       */
  /* .................................................................... */

  /**
   * Get the Boolean sort.
   * @return Sort Boolean.
   */
  public Sort getBooleanSort()
  {
    long sortPointer = getBooleanSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getBooleanSort(long pointer);

  /**
   * Get the integer sort.
   * @return Sort Integer.
   */
  public Sort getIntegerSort()
  {
    long sortPointer = getIntegerSort(pointer);
    return new Sort(sortPointer);
  }

  public native long getIntegerSort(long pointer);
  /**
   * Get the real sort.
   * @return Sort Real.
   */
  public Sort getRealSort()
  {
    long sortPointer = getRealSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getRealSort(long pointer);
  /**
   * Get the regular expression sort.
   * @return Sort RegExp.
   */
  public Sort getRegExpSort()
  {
    long sortPointer = getRegExpSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getRegExpSort(long pointer);
  /**
   * Get the floating-point rounding mode sort.
   * @return Sort RoundingMode.
   * @throws CVC5ApiException
   */
  public Sort getRoundingModeSort() throws CVC5ApiException
  {
    long sortPointer = getRoundingModeSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getRoundingModeSort(long pointer) throws CVC5ApiException;

  /**
   * Get the string sort.
   * @return Sort String.
   */
  public Sort getStringSort()
  {
    long sortPointer = getStringSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getStringSort(long solverPointer);
  /**
   * Create an array sort.
   * @param indexSort The array index sort.
   * @param elemSort The array element sort.
   * @return The array sort.
   */
  public Sort mkArraySort(Sort indexSort, Sort elemSort)
  {
    long sortPointer = mkArraySort(pointer, indexSort.getPointer(), elemSort.getPointer());
    return new Sort(sortPointer);
  }

  private native long mkArraySort(long pointer, long indexSortPointer, long elementSortPointer);

  /**
   * Create a bit-vector sort.
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector sort.
   * @throws CVC5ApiException
   */
  public Sort mkBitVectorSort(int size) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    long sortPointer = mkBitVectorSort(pointer, size);
    return new Sort(sortPointer);
  }

  private native long mkBitVectorSort(long pointer, int size);

  /**
   * Create a finite field sort.
   * @param size The size of the finite field sort.
   * @param base The base of the string representation.
   * @return The finite field sort.
   * @throws CVC5ApiException
   */
  public Sort mkFiniteFieldSort(String size, int base) throws CVC5ApiException
  {
    long sortPointer = mkFiniteFieldSort(pointer, size, base);
    return new Sort(sortPointer);
  }

  private native long mkFiniteFieldSort(long pointer, String size, int base);

  /**
   * Create a floating-point sort.
   * @param exp The bit-width of the exponent of the floating-point sort.
   * @param sig The bit-width of the significand of the floating-point sort.
   * @return The floating-point sort.
   * @throws CVC5ApiException
   */
  public Sort mkFloatingPointSort(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long sortPointer = mkFloatingPointSort(pointer, exp, sig);
    return new Sort(sortPointer);
  }

  private native long mkFloatingPointSort(long solverPointer, int exp, int sig);

  /**
   * Create a datatype sort.
   * @param dtypedecl The datatype declaration from which the sort is created.
   * @return The datatype sort.
   * @throws CVC5ApiException
   */
  public Sort mkDatatypeSort(DatatypeDecl dtypedecl) throws CVC5ApiException
  {
    long pointer = mkDatatypeSort(this.pointer, dtypedecl.getPointer());
    return new Sort(pointer);
  }

  private native long mkDatatypeSort(long pointer, long datatypeDeclPointer)
      throws CVC5ApiException;

  /**
   * Create a vector of datatype sorts.
   *
   * The names of the datatype declarations must be distinct.
   *
   * @param dtypedecls The datatype declarations from which the sort is created.
   * @return The datatype sorts.
   * @throws CVC5ApiException
   */
  public Sort[] mkDatatypeSorts(DatatypeDecl[] dtypedecls) throws CVC5ApiException
  {
    long[] declPointers = Utils.getPointers(dtypedecls);
    long[] sortPointers = mkDatatypeSorts(pointer, declPointers);
    Sort[] sorts = Utils.getSorts(sortPointers);
    return sorts;
  }

  private native long[] mkDatatypeSorts(long pointer, long[] declPointers) throws CVC5ApiException;

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
    long sortPointer = mkFunctionSort(pointer, Utils.getPointers(sorts), codomain.getPointer());
    return new Sort(sortPointer);
  }

  private native long mkFunctionSort(long pointer, long[] sortPointers, long codomainPointer);

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
    long sortPointer = mkParamSort(pointer, symbol);
    return new Sort(sortPointer);
  }

  private native long mkParamSort(long pointer, String symbol);

  /**
   * Create a sort parameter.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The sort parameter.
   */
  public Sort mkParamSort()
  {
    long sortPointer = mkParamSort(pointer);
    return new Sort(sortPointer);
  }

  private native long mkParamSort(long pointer);

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
    long skolemPointer = mkSkolem(pointer, skolemId.getValue(), Utils.getPointers(indices));
    return new Term(skolemPointer);
  }

  private native long mkSkolem(long pointer, int skolemId, long[] indices);

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
    int numIndices = getNumIndicesForSkolemId(pointer, id.getValue());
    return numIndices;
  }

  private native int getNumIndicesForSkolemId(long pointer, int skolemId);

  /**
   * Create a predicate sort.
   * @param sorts The list of sorts of the predicate.
   * @return The predicate sort.
   */
  public Sort mkPredicateSort(Sort[] sorts)
  {
    long sortPointer = mkPredicateSort(pointer, Utils.getPointers(sorts));
    return new Sort(sortPointer);
  }

  private native long mkPredicateSort(long pointer, long[] sortPointers);

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
    long sortPointer = mkRecordSort(pointer, Utils.getPairs(fields));
    return new Sort(sortPointer);
  }

  private native long mkRecordSort(long pointer, Pair<String, Long>[] fields);

  /**
   * Create a set sort.
   * @param elemSort The sort of the set elements.
   * @return The set sort.
   */
  public Sort mkSetSort(Sort elemSort)
  {
    long sortPointer = mkSetSort(pointer, elemSort.getPointer());
    return new Sort(sortPointer);
  }

  private native long mkSetSort(long pointer, long elemSortPointer);
  /**
   * Create a bag sort.
   * @param elemSort The sort of the bag elements.
   * @return The bag sort.
   */
  public Sort mkBagSort(Sort elemSort)
  {
    long sortPointer = mkBagSort(pointer, elemSort.getPointer());
    return new Sort(sortPointer);
  }

  private native long mkBagSort(long pointer, long elemSortPointer);

  /**
   * Create a sequence sort.
   * @param elemSort The sort of the sequence elements.
   * @return The sequence sort.
   */
  public Sort mkSequenceSort(Sort elemSort)
  {
    long sortPointer = mkSequenceSort(pointer, elemSort.getPointer());
    return new Sort(sortPointer);
  }

  private native long mkSequenceSort(long pointer, long elemSortPointer);

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
    long sortPointer = mkAbstractSort(pointer, kind.getValue());
    return new Sort(sortPointer);
  }

  private native long mkAbstractSort(long pointer, int kindValue);

  /**
   * Create an uninterpreted sort.
   * @param symbol The name of the sort.
   * @return The uninterpreted sort.
   */
  public Sort mkUninterpretedSort(String symbol)
  {
    long sortPointer = mkUninterpretedSort(pointer, symbol);
    return new Sort(sortPointer);
  }

  private native long mkUninterpretedSort(long pointer, String symbol);

  /**
   * Create an uninterpreted sort.
   * @return The uninterpreted sort.
   */
  public Sort mkUninterpretedSort()
  {
    long sortPointer = mkUninterpretedSort(pointer);
    return new Sort(sortPointer);
  }

  private native long mkUninterpretedSort(long pointer);

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive parametric datatypes.
   *
   * @param symbol The symbol of the sort.
   * @param arity The number of sort parameters of the sort.
   * @return The unresolved sort.
   * @throws CVC5ApiException
   */
  public Sort mkUnresolvedDatatypeSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = mkUnresolvedDatatypeSort(pointer, symbol, arity);
    return new Sort(sortPointer);
  }

  private native long mkUnresolvedDatatypeSort(long pointer, String symbol, int arity);

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive datatypes without sort parameters.
   *
   * @param symbol The symbol of the sort.
   * @return The unresolved sort.
   * @throws CVC5ApiException
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
   * @throws CVC5ApiException
   */
  public Sort mkUninterpretedSortConstructorSort(int arity, String symbol) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = mkUninterpretedSortConstructorSort(pointer, arity, symbol);
    return new Sort(sortPointer);
  }

  private native long mkUninterpretedSortConstructorSort(long pointer, int arity, String symbol);

  /**
   * Create a sort constructor sort.
   *
   * An uninterpreted sort constructor is an uninterpreted sort with
   * arity &gt; 0.
   *
   * @param arity The arity of the sort (must be &gt; 0)
   * @return The sort constructor sort.
   * @throws CVC5ApiException
   */
  public Sort mkUninterpretedSortConstructorSort(int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = mkUninterpretedSortConstructorSort(pointer, arity);
    return new Sort(sortPointer);
  }

  private native long mkUninterpretedSortConstructorSort(long pointer, int arity);

  /**
   * Create a tuple sort.
   * @param sorts Of the elements of the tuple.
   * @return The tuple sort.
   */
  public Sort mkTupleSort(Sort[] sorts)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long sortPointer = mkTupleSort(pointer, sortPointers);
    return new Sort(sortPointer);
  }

  private native long mkTupleSort(long pointer, long[] sortPointers);

  /**
   * Create a nullable sort.
   *
   * @param sort The sort of the element of the nullable.
   * @return The nullable sort.
   */
  public Sort mkNullableSort(Sort sort)
  {
    long sortPointer = mkNullableSort(pointer, sort.getPointer());
    return new Sort(sortPointer);
  }

  private native long mkNullableSort(long pointer, long sortPointer);

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
    long termPointer = mkTerm(pointer, kind.getValue());
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, int kindValue);

  /**
   * Create a unary term of given kind.
   * @param kind The kind of the term.
   * @param child The child of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term child)
  {
    long termPointer = mkTerm(pointer, kind.getValue(), child.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, int kindValue, long childPointer);

  /**
   * Create binary term of given kind.
   * @param kind The kind of the term.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term child1, Term child2)
  {
    long termPointer = mkTerm(pointer, kind.getValue(), child1.getPointer(), child2.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, int kindValue, long child1Pointer, long child2Pointer);

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
    long termPointer = mkTerm(
        pointer, kind.getValue(), child1.getPointer(), child2.getPointer(), child3.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(
      long pointer, int kindValue, long child1Pointer, long child2Pointer, long child3Pointer);
  /**
   * Create n-ary term of given kind.
   * @param kind The kind of the term.
   * @param children The children of the term.
   * @return The Term.
   */
  public Term mkTerm(Kind kind, Term[] children)
  {
    long[] childPointers = Utils.getPointers(children);
    long termPointer = mkTerm(pointer, kind.getValue(), childPointers);
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, int kindValue, long[] childrenPointers);

  /**
   * Create nullary term of given kind from a given operator.
   * Create operators with {@link TermManager#mkOp(Kind)},
   * {@link TermManager#mkOp(Kind, String)}, {@link TermManager#mkOp(Kind, int[])}.
   * @param op The operator.
   * @return The Term.
   */
  public Term mkTerm(Op op)
  {
    long termPointer = mkTerm(pointer, op.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, long opPointer);
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
    long termPointer = mkTerm(pointer, op.getPointer(), child.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, long opPointer, long childPointer);

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
    long termPointer = mkTerm(pointer, op.getPointer(), child1.getPointer(), child2.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, long opPointer, long child1Pointer, long child2Pointer);
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
    long termPointer = mkTerm(
        pointer, op.getPointer(), child1.getPointer(), child2.getPointer(), child3.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(
      long pointer, long opPointer, long child1Pointer, long child2Pointer, long child3Pointer);

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
    long[] childPointers = Utils.getPointers(children);
    long termPointer = mkTerm(pointer, op.getPointer(), childPointers);
    return new Term(termPointer);
  }

  private native long mkTerm(long pointer, long opPointer, long[] childrenPointers);

  /**
   * Create a tuple term.
   * Terms are automatically converted if sorts are compatible.
   * @param terms The elements in the tuple.
   * @return The tuple Term.
   */
  public Term mkTuple(Term[] terms)
  {
    long[] termPointers = Utils.getPointers(terms);
    long termPointer = mkTuple(pointer, termPointers);
    return new Term(termPointer);
  }

  private native long mkTuple(long pointer, long[] termPointers);

  /**
   * Create a nullable some term.
   * @param term The element value.
   * @return the Element value wrapped in some constructor.
   */
  public Term mkNullableSome(Term term)
  {
    long termPointer = mkNullableSome(pointer, term.getPointer());
    return new Term(termPointer);
  }

  private native long mkNullableSome(long pointer, long termPointer);

  /**
   * Create a selector for nullable term.
   * @param term A nullable term.
   * @return The element value of the nullable term.
   */
  public Term mkNullableVal(Term term)
  {
    long termPointer = mkNullableVal(pointer, term.getPointer());
    return new Term(termPointer);
  }

  private native long mkNullableVal(long pointer, long termPointer);

  /**
   * Create a null tester for a nullable term.
   * @param term A nullable term.
   * @return A tester whether term is null.
   */
  public Term mkNullableIsNull(Term term)
  {
    long termPointer = mkNullableIsNull(pointer, term.getPointer());
    return new Term(termPointer);
  }

  private native long mkNullableIsNull(long pointer, long termPointer);

  /**
   * Create a some tester for a nullable term.
   * @param term A nullable term.
   * @return A tester whether term is some.
   */
  public Term mkNullableIsSome(Term term)
  {
    long termPointer = mkNullableIsSome(pointer, term.getPointer());
    return new Term(termPointer);
  }

  private native long mkNullableIsSome(long pointer, long termPointer);

  /**
   * Create a constant representing a null value of the given sort.
   * @param sort The sort of the Nullable element.
   * @return The null constant.
   */
  public Term mkNullableNull(Sort sort)
  {
    long termPointer = mkNullableNull(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkNullableNull(long pointer, long sortPointer);
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
    long[] termPointers = Utils.getPointers(args);
    long termPointer = mkNullableLift(pointer, kind.getValue(), termPointers);
    return new Term(termPointer);
  }

  private native long mkNullableLift(long pointer, int kindValue, long[] termPointers);

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
    long opPointer = mkOp(pointer, kind.getValue());
    return new Op(opPointer);
  }

  private native long mkOp(long pointer, int kindValue);
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
    long opPointer = mkOp(pointer, kind.getValue(), arg);
    return new Op(opPointer);
  }

  private native long mkOp(long pointer, int kindValue, String arg);

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
   * @throws CVC5ApiException
   */
  public Op mkOp(Kind kind, int arg) throws CVC5ApiException
  {
    Utils.validateUnsigned(arg, "arg");
    long opPointer = mkOp(pointer, kind.getValue(), arg);
    return new Op(opPointer);
  }

  private native long mkOp(long pointer, int kindValue, int arg);

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
   * @throws CVC5ApiException
   */
  public Op mkOp(Kind kind, int arg1, int arg2) throws CVC5ApiException
  {
    Utils.validateUnsigned(arg1, "arg1");
    Utils.validateUnsigned(arg2, "arg2");
    long opPointer = mkOp(pointer, kind.getValue(), arg1, arg2);
    return new Op(opPointer);
  }

  private native long mkOp(long pointer, int kindValue, int arg1, int arg2);

  /**
   * Create operator of Kind:
   * <ul>
   *   <li>TUPLE_PROJECT</li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   * @param kind The kind of the operator.
   * @param args The arguments (indices) of the operator.
   * @return The operator.
   * @throws CVC5ApiException
   */
  public Op mkOp(Kind kind, int[] args) throws CVC5ApiException
  {
    Utils.validateUnsigned(args, "args");
    long opPointer = mkOp(pointer, kind.getValue(), args);
    return new Op(opPointer);
  }

  private native long mkOp(long pointer, int kindValue, int[] args);

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */

  /**
   * Create a Boolean {@code true} constant.
   * @return The true constant.
   */
  public Term mkTrue()
  {
    long termPointer = mkTrue(pointer);
    return new Term(termPointer);
  }

  private native long mkTrue(long pointer);
  /**
   * Create a Boolean {@code false} constant.
   * @return The false constant.
   */
  public Term mkFalse()
  {
    long termPointer = mkFalse(pointer);
    return new Term(termPointer);
  }

  private native long mkFalse(long pointer);
  /**
   * Create a Boolean constant.
   * @param val The value of the constant.
   * @return The Boolean constant.
   */
  public Term mkBoolean(boolean val)
  {
    long termPointer = mkBoolean(pointer, val);
    return new Term(termPointer);
  }

  private native long mkBoolean(long pointer, boolean val);
  /**
   * Create a constant representing the number Pi.
   * @return A constant representing Pi.
   */
  public Term mkPi()
  {
    long termPointer = mkPi(pointer);
    return new Term(termPointer);
  }

  private native long mkPi(long pointer);
  /**
   * Create an integer constant from a string.
   * @param s The string representation of the constant, may represent an.
   *          integer (e.g., "123").
   * @return A constant of sort Integer assuming {@code s} represents an
   *         integer).
   * @throws CVC5ApiException
   */
  public Term mkInteger(String s) throws CVC5ApiException
  {
    long termPointer = mkInteger(pointer, s);
    return new Term(termPointer);
  }

  private native long mkInteger(long pointer, String s) throws CVC5ApiException;

  /**
   * Create an integer constant from a C++ {@code int}.
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  public Term mkInteger(long val)
  {
    long termPointer = mkInteger(pointer, val);
    return new Term(termPointer);
  }

  private native long mkInteger(long pointer, long val);
  /**
   * Create a real constant from a string.
   * @param s The string representation of the constant, may represent an.
   *          integer (e.g., "123") or real constant (e.g., "12.34" or
   * "12/34").
   * @return A constant of sort Real.
   * @throws CVC5ApiException
   */
  public Term mkReal(String s) throws CVC5ApiException
  {
    long termPointer = mkReal(pointer, s);
    return new Term(termPointer);
  }

  private native long mkReal(long pointer, String s) throws CVC5ApiException;
  /**
   * Create a real constant from an integer.
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  public Term mkReal(long val)
  {
    long termPointer = mkRealValue(pointer, val);
    return new Term(termPointer);
  }

  private native long mkRealValue(long pointer, long val);
  /**
   * Create a real constant from a rational.
   * @param num The value of the numerator.
   * @param den The value of the denominator.
   * @return A constant of sort Real.
   */
  public Term mkReal(long num, long den)
  {
    long termPointer = mkReal(pointer, num, den);
    return new Term(termPointer);
  }

  private native long mkReal(long pointer, long num, long den);

  /**
   * Create a regular expression none ({@code re.none}) term.
   * @return The none term.
   */
  public Term mkRegexpNone()
  {
    long termPointer = mkRegexpNone(pointer);
    return new Term(termPointer);
  }

  private native long mkRegexpNone(long pointer);

  /**
   * Create a regular expression all ({@code re.all}) term.
   * @return The all term.
   */
  public Term mkRegexpAll()
  {
    long termPointer = mkRegexpAll(pointer);
    return new Term(termPointer);
  }

  private native long mkRegexpAll(long pointer);

  /**
   * Create a regular expression allchar ({@code re.allchar}) term.
   * @return The allchar term.
   */
  public Term mkRegexpAllchar()
  {
    long termPointer = mkRegexpAllchar(pointer);
    return new Term(termPointer);
  }

  private native long mkRegexpAllchar(long pointer);

  /**
   * Create a constant representing an empty set of the given sort.
   * @param sort The sort of the set elements.
   * @return The empty set constant.
   */
  public Term mkEmptySet(Sort sort)
  {
    long termPointer = mkEmptySet(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkEmptySet(long pointer, long sortPointer);
  /**
   * Create a constant representing an empty bag of the given sort.
   * @param sort The sort of the bag elements.
   * @return The empty bag constant.
   */
  public Term mkEmptyBag(Sort sort)
  {
    long termPointer = mkEmptyBag(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkEmptyBag(long pointer, long sortPointer);

  /**
   * Create a separation logic empty term.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The separation logic empty term.
   */
  public Term mkSepEmp()
  {
    long termPointer = mkSepEmp(pointer);
    return new Term(termPointer);
  }

  private native long mkSepEmp(long pointer);

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
    long termPointer = mkSepNil(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkSepNil(long pointer, long sortPointer);

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
    long termPointer = mkString(pointer, s, useEscSequences);
    return new Term(termPointer);
  }

  private native long mkString(long pointer, String s, boolean useEscSequences);

  /**
   * Create a String constant.
   * @param s A list of unsigned (unicode) values this constant represents
   *          as string.
   * @return The String constant.
   * @throws CVC5ApiException
   */
  public Term mkString(int[] s) throws CVC5ApiException
  {
    Utils.validateUnsigned(s, "s");
    long termPointer = mkString(pointer, s);
    return new Term(termPointer);
  }

  private native long mkString(long pointer, int[] s);

  /**
   * Create an empty sequence of the given element sort.
   * @param sort The element sort of the sequence.
   * @return The empty sequence with given element sort.
   */
  public Term mkEmptySequence(Sort sort)
  {
    long termPointer = mkEmptySequence(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkEmptySequence(long pointer, long sortPointer);

  /**
   * Create a universe set of the given sort.
   * @param sort The sort of the set elements.
   * @return The universe set constant.
   */
  public Term mkUniverseSet(Sort sort)
  {
    long termPointer = mkUniverseSet(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkUniverseSet(long pointer, long sortPointer);

  /**
   * Create a bit-vector constant of given size and value = 0.
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector constant.
   * @throws CVC5ApiException
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
   * @throws CVC5ApiException
   */
  public Term mkBitVector(int size, long val) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    Utils.validateUnsigned(val, "val");
    long termPointer = mkBitVector(pointer, size, val);
    return new Term(termPointer);
  }

  private native long mkBitVector(long pointer, int size, long val);

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
   * @throws CVC5ApiException
   */
  public Term mkBitVector(int size, String s, int base) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    Utils.validateUnsigned(base, "base");
    long termPointer = mkBitVector(pointer, size, s, base);
    return new Term(termPointer);
  }

  private native long mkBitVector(long pointer, int size, String s, int base);

  /**
   * Create a finite field constant in a given field and for a given value.
   *
   * @api.note The given value must fit into a the given finite field.
   *
   * @param val The value of the constant.
   * @param sort The sort of the finite field.
   * @param base The base of the string representation.
   * @return The finite field constant.
   * @throws CVC5ApiException
   */
  public Term mkFiniteFieldElem(String val, Sort sort, int base) throws CVC5ApiException
  {
    long termPointer = mkFiniteFieldElem(pointer, val, sort.getPointer(), base);
    return new Term(termPointer);
  }

  private native long mkFiniteFieldElem(long pointer, String val, long sortPointer, int base);

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
    long termPointer = mkConstArray(pointer, sort.getPointer(), val.getPointer());
    return new Term(termPointer);
  }

  private native long mkConstArray(long pointer, long sortPointer, long valPointer);
  /**
   * Create a positive infinity floating-point constant (SMT-LIB: {@code +oo}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPointPosInf(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointPosInf(pointer, exp, sig);
    return new Term(termPointer);
  }

  private native long mkFloatingPointPosInf(long pointer, int exp, int sig);
  /**
   * Create a negative infinity floating-point constant (SMT-LIB: {@code -oo}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPointNegInf(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointNegInf(pointer, exp, sig);
    return new Term(termPointer);
  }

  private native long mkFloatingPointNegInf(long pointer, int exp, int sig);
  /**
   * Create a not-a-number floating-point constant (SMT-LIB: {@code NaN}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPointNaN(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointNaN(pointer, exp, sig);
    return new Term(termPointer);
  }

  private native long mkFloatingPointNaN(long pointer, int exp, int sig);

  /**
   * Create a positive zero floating-point constant (SMT-LIB: {@code +zero}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPointPosZero(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointPosZero(pointer, exp, sig);
    return new Term(termPointer);
  }

  private native long mkFloatingPointPosZero(long pointer, int exp, int sig);

  /**
   * Create a negative zero floating-point constant (SMT-LIB: {@code -zero}).
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPointNegZero(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointNegZero(pointer, exp, sig);
    return new Term(termPointer);
  }

  private native long mkFloatingPointNegZero(long pointer, int exp, int sig);

  /**
   * Create a rounding mode constant.
   * @param rm The floating point rounding mode this constant represents.
   * @return The rounding mode.
   */
  public Term mkRoundingMode(RoundingMode rm)
  {
    long termPointer = mkRoundingMode(pointer, rm.getValue());
    return new Term(termPointer);
  }

  private native long mkRoundingMode(long pointer, int rm);

  /**
   * Create a floating-point value from a bit-vector given in IEEE-754
   * format.
   * @param exp Size of the exponent.
   * @param sig Size of the significand.
   * @param val Value of the floating-point constant as a bit-vector term.
   * @return The floating-point value.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPoint(int exp, int sig, Term val) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPoint(pointer, exp, sig, val.getPointer());
    return new Term(termPointer);
  }

  private native long mkFloatingPoint(long pointer, int exp, int sig, long valPointer);

  /**
   * Create a floating-point value from its three IEEE-754 bit-vector value
   * components (sign bit, exponent, significand).
   * @param sign The sign bit.
   * @param exp  The bit-vector representing the exponent.
   * @param sig The bit-vector representing the significand.
   * @return The floating-point value.
   * @throws CVC5ApiException
   */
  public Term mkFloatingPoint(Term sign, Term exp, Term sig) throws CVC5ApiException
  {
    long termPointer =
        mkFloatingPointX(pointer, sign.getPointer(), exp.getPointer(), sig.getPointer());
    return new Term(termPointer);
  }

  private native long mkFloatingPointX(
      long pointer, long signPointer, long expPointer, long sigPointer);

  /**
   * Create a cardinality constraint for an uninterpreted sort.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sort The sort the cardinality constraint is for.
   * @param upperBound The upper bound on the cardinality of the sort.
   * @return The cardinality constraint.
   * @throws CVC5ApiException
   */
  public Term mkCardinalityConstraint(Sort sort, int upperBound) throws CVC5ApiException
  {
    Utils.validateUnsigned(upperBound, "upperBound");
    long termPointer = mkCardinalityConstraint(pointer, sort.getPointer(), upperBound);
    return new Term(termPointer);
  }

  private native long mkCardinalityConstraint(long pointer, long sortPointer, int upperBound);

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
    long termPointer = mkConst(pointer, sort.getPointer(), symbol);
    return new Term(termPointer);
  }

  private native long mkConst(long pointer, long sortPointer, String symbol);

  /**
   * Create a free constant with a default symbol name.
   *
   * @param sort The sort of the constant.
   * @return The first-order constant.
   */
  public Term mkConst(Sort sort)
  {
    long termPointer = mkConst(pointer, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkConst(long pointer, long sortPointer);

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
    long termPointer = mkVar(pointer, sort.getPointer(), symbol);
    return new Term(termPointer);
  }

  private native long mkVar(long pointer, long sortPointer, String symbol);

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
    long declPointer = mkDatatypeConstructorDecl(pointer, name);
    return new DatatypeConstructorDecl(declPointer);
  }

  private native long mkDatatypeConstructorDecl(long pointer, String name);

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
    long declPointer = mkDatatypeDecl(pointer, name, isCoDatatype);
    return new DatatypeDecl(declPointer);
  }

  private native long mkDatatypeDecl(long pointer, String name, boolean isCoDatatype);

  /**
   * Create a datatype declaration.
   *
   * Create sorts parameter with {@link Solver#mkParamSort(String)}.
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
   * Create sorts parameter with {@link Solver#mkParamSort(String)}.
   *
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params, boolean isCoDatatype)
  {
    long[] paramPointers = Utils.getPointers(params);
    long declPointer = mkDatatypeDecl(pointer, name, paramPointers, isCoDatatype);
    return new DatatypeDecl(declPointer);
  }

  private native long mkDatatypeDecl(
      long pointer, String name, long[] paramPointers, boolean isCoDatatype);
}
