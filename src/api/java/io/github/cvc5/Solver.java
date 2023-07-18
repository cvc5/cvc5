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

import io.github.cvc5.modes.BlockModelsMode;
import io.github.cvc5.modes.LearnedLitType;
import io.github.cvc5.modes.ProofComponent;
import java.io.IOException;
import java.util.*;

/**
 * A cvc5 solver.
 */
public class Solver implements IPointer
{
  static
  {
    Utils.loadLibraries();
  }

  private long pointer;

  public long getPointer()
  {
    return pointer;
  }

  private native long newSolver();

  public void deletePointer()
  {
    if (pointer != 0)
    {
      deletePointer(pointer);
    }
    pointer = 0;
  }

  private static native void deletePointer(long pointer);

  // store IOracle objects
  List<IOracle> oracles = new ArrayList<>();

  /* .................................................................... */
  /* Constructors                                                         */
  /* .................................................................... */

  public Solver()
  {
    this.pointer = newSolver();
  }

  /* .................................................................... */
  /* Sorts Handling                                                       */
  /* .................................................................... */

  /**
   * @return Sort Boolean.
   */
  public Sort getBooleanSort()
  {
    long sortPointer = getBooleanSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getBooleanSort(long pointer);

  /**
   * @return Sort Integer.
   */
  public Sort getIntegerSort()
  {
    long sortPointer = getIntegerSort(pointer);
    return new Sort(sortPointer);
  }

  public native long getIntegerSort(long pointer);
  /**
   * @return Sort Real.
   */
  public Sort getRealSort()
  {
    long sortPointer = getRealSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getRealSort(long pointer);
  /**
   * @return Sort RegExp.
   */
  public Sort getRegExpSort()
  {
    long sortPointer = getRegExpSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getRegExpSort(long pointer);
  /**
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
   * @return The finite field sort.
   * @throws CVC5ApiException
   */
  public Sort mkFiniteFieldSort(String size) throws CVC5ApiException
  {
    long sortPointer = mkFiniteFieldSort(pointer, size);
    return new Sort(sortPointer);
  }

  private native long mkFiniteFieldSort(long pointer, String size);

  /**
   * Create a floating-point sort.
   * @param exp The bit-width of the exponent of the floating-point sort.
   * @param sig The bit-width of the significand of the floating-point sort.
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
   * The {@link SortKind} k must be the kind of a sort that can be abstracted, i.e., a sort
   * that has indices or argument sorts. For example, {@link SortKind#ARRAY_SORT} and
   *  {@link SortKind#BITVECTOR_SORT} can be passed as the {@link SortKind} k to this method, while
   *  {@link SortKind#INTEGER_SORT} and  {@link SortKind#STRING_SORT} cannot.
   *
   * @api.note Providing the kind  {@link SortKind#ABSTRACT_SORT} as an argument to this method
   * returns the (fully) unspecified sort, often denoted {@code ?}.
   *
   * @api.note Providing a kind {@code k} that has no indices and a fixed arity
   * of argument sorts will return the sort of {@link SortKind} k whose arguments
   * are the unspecified sort. For example, mkAbstractSort(ARRAY_SORT) will
   * return the sort (ARRAY_SORT ? ?) instead of the abstract sort whose abstract
   * kind is {@link SortKind#ABSTRACT_SORT}.
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

  /* .................................................................... */
  /* Create Terms                                                         */
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
   * Create operators with mkOp().
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
   * Create operators with mkOp().
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
   * Create operators with mkOp().
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
   * Create operators with mkOp().
   * @param op The operator.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @param child3 The third child of the term.
   * @return The Term.
   */
  public Term mkTerm(Op op, Term child1, Term child2, Term child3)
  {
    long termPointer =
        mkTerm(op.getPointer(), child1.getPointer(), child2.getPointer(), child3.getPointer());
    return new Term(termPointer);
  }

  private native long mkTerm(
      long pointer, long opPointer, long child1Pointer, long child2Pointer, long child3Pointer);

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
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
   * Create a tuple term. Terms are automatically converted if sorts are
   * compatible.
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
   * @return The Boolean constant.
   * @param val The value of the constant.
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
    // TODO: review unicode
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
   * @return The finite field constant.
   * @throws CVC5ApiException
   */
  public Term mkFiniteFieldElem(String val, Sort sort) throws CVC5ApiException
  {
    long termPointer = mkFiniteFieldElem(pointer, val, sort.getPointer());
    return new Term(termPointer);
  }

  private native long mkFiniteFieldElem(long pointer, String val, long sortPointer);

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

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a formula without doing "much" work.
   *
   * Does not involve the SAT Engine in the simplification, but uses the
   * current definitions, assertions, and the current partial model, if one has
   * been constructed.  It also involves theory normalization.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param t The formula to simplify.
   * @return The simplified formula.
   */
  public Term simplify(Term t)
  {
    long termPointer = simplify(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long simplify(long pointer, long termPointer);

  /**
   * Assert a formula.
   * SMT-LIB:
   * {@code
   *   ( assert <term> )
   * }
   * @param term The formula to assert.
   */
  public void assertFormula(Term term)
  {
    assertFormula(pointer, term.getPointer());
  }

  private native void assertFormula(long pointer, long termPointer);

  /**
   * Check satisfiability.
   *
   * SMT-LIB:
   * {@code
   *   ( check-sat )
   * }
   *
   * @return The result of the satisfiability check.
   */
  public Result checkSat()
  {
    long resultPointer = checkSat(pointer);
    return new Result(resultPointer);
  }

  private native long checkSat(long pointer);
  /**
   * Check satisfiability assuming the given formula.
   *
   * SMT-LIB:
   * {@code
   *   ( check-sat-assuming ( <prop_literal> ) )
   * }
   *
   * @param assumption The formula to assume.
   * @return The result of the satisfiability check.
   */
  public Result checkSatAssuming(Term assumption)
  {
    long resultPointer = checkSatAssuming(pointer, assumption.getPointer());
    return new Result(resultPointer);
  }

  private native long checkSatAssuming(long pointer, long assumptionPointer);

  /**
   * Check satisfiability assuming the given formulas.
   *
   * SMT-LIB:
   * {@code
   *   ( check-sat-assuming ( <prop_literal>+ ) )
   * }
   *
   * @param assumptions The formulas to assume.
   * @return The result of the satisfiability check.
   */
  public Result checkSatAssuming(Term[] assumptions)
  {
    long[] pointers = Utils.getPointers(assumptions);
    long resultPointer = checkSatAssuming(pointer, pointers);
    return new Result(resultPointer);
  }

  private native long checkSatAssuming(long pointer, long[] assumptionPointers);

  /**
   * Create datatype sort.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-datatype <symbol> <datatype_decl> )
   * }
   *
   * @param symbol The name of the datatype sort.
   * @param ctors The constructor declarations of the datatype sort.
   * @return The datatype sort.
   */
  public Sort declareDatatype(String symbol, DatatypeConstructorDecl[] ctors)
  {
    long[] pointers = Utils.getPointers(ctors);
    long sortPointer = declareDatatype(pointer, symbol, pointers);
    return new Sort(sortPointer);
  }

  private native long declareDatatype(long pointer, String symbol, long[] declPointers);

  /**
   * Declare n-ary function symbol.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-fun <symbol> ( <sort>* ) <sort> )
   * }
   *
   * @param symbol The name of the function.
   * @param sorts The sorts of the parameters to this function.
   * @param sort The sort of the return value of this function.
   * @return The function.
   */
  public Term declareFun(String symbol, Sort[] sorts, Sort sort)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareFun(pointer, symbol, sortPointers, sort.getPointer());
    return new Term(termPointer);
  }

  private native long declareFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer);

  /**
   * Declare uninterpreted sort.
   *
   * SMT-LIB:
   * {@code
   *   ( declare-sort <symbol> <numeral> )
   * }
   *
   * @api.note This corresponds to mkUninterpretedSort() const if arity = 0, and
   *           to mkUninterpretedSortConstructorSort() const if arity &gt; 0.
   *
   * @param symbol The name of the sort.
   * @param arity The arity of the sort.
   * @return The sort.
   * @throws CVC5ApiException
   */
  public Sort declareSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = declareSort(pointer, symbol, arity);
    return new Sort(sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity);

  /**
   * Define n-ary function in the current context.
   *
   * SMT-LIB:
   * {@code
   *   ( define-fun <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @return The function.
   */
  public Term defineFun(String symbol, Term[] boundVars, Sort sort, Term term)
  {
    return defineFun(symbol, boundVars, sort, term, false);
  }

  /**
   * Define n-ary function.
   *
   * SMT-LIB:
   * {@code
   *   ( define-fun <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  public Term defineFun(String symbol, Term[] boundVars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        defineFun(pointer, symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(termPointer);
  }

  private native long defineFun(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @return The function.
   */
  public Term defineFunRec(String symbol, Term[] boundVars, Sort sort, Term term)
  {
    return defineFunRec(symbol, boundVars, sort, term, false);
  }

  /**
   * Define recursive function.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  public Term defineFunRec(String symbol, Term[] boundVars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = defineFunRec(
        pointer, symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(termPointer);
  }

  private native long defineFunRec(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * Create parameter {@code fun} with {@link Solver#mkConst(Sort)}.
   *
   * @param fun The sorted function.
   * @param boundVars The parameters to this function.
   * @param term The function body.
   * @return The function.
   */

  public Term defineFunRec(Term fun, Term[] boundVars, Term term)
  {
    return defineFunRec(fun, boundVars, term, false);
  }

  /**
   * Define recursive function.
   *
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   *
   * Create parameter {@code fun} with {@link Solver#mkConst(Sort)}.
   *
   * @param fun The sorted function.
   * @param boundVars The parameters to this function.
   * @param term The function body.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   * @return The function.
   */
  public Term defineFunRec(Term fun, Term[] boundVars, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        defineFunRec(pointer, fun.getPointer(), boundVarPointers, term.getPointer(), global);
    return new Term(termPointer);
  }

  private native long defineFunRec(
      long pointer, long funPointer, long[] boundVarPointers, long termPointer, boolean global);

  /**
   * Define recursive functions in the current context.
   *
   * SMT-LIB:
   * {@code
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * }
   *
   * Create elements of parameter {@code funs} with
   * {@link Solver#mkConst(Sort)}.
   *
   * @param funs The sorted functions.
   * @param boundVars The list of parameters to the functions.
   * @param terms The list of function bodies of the functions.
   */
  public void defineFunsRec(Term[] funs, Term[][] boundVars, Term[] terms)
  {
    defineFunsRec(funs, boundVars, terms, false);
  }
  /**
   * Define recursive functions.
   *
   * SMT-LIB:
   * {@code
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * }
   *
   * Create elements of parameter {@code funs} with
   * {@link Solver#mkConst(Sort)}.
   *
   * @param funs The sorted functions.
   * @param boundVars The list of parameters to the functions.
   * @param terms The list of function bodies of the functions.
   * @param global Determines whether this definition is global (i.e., persists
   *               when popping the context).
   */
  public void defineFunsRec(Term[] funs, Term[][] boundVars, Term[] terms, boolean global)
  {
    long[] funPointers = Utils.getPointers(funs);
    long[][] boundVarPointers = Utils.getPointers(boundVars);
    long[] termPointers = Utils.getPointers(terms);
    defineFunsRec(pointer, funPointers, boundVarPointers, termPointers, global);
  }

  private native void defineFunsRec(long pointer,
      long[] funPointers,
      long[][] boundVarPointers,
      long[] termPointers,
      boolean global);

  /**
   * Get a list of input literals that are entailed by the current set of
   * assertions.
   *
   * SMT-LIB:
   * {@code
   * ( get-learned-literals )
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The list of learned literals.
   */
  public Term[] getLearnedLiterals()
  {
    long[] retPointers = getLearnedLiterals(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getLearnedLiterals(long pointer);

  /**
   * Get a list of literals that are entailed by the current set of assertions.
   *
   * SMT-LIB:
   * {@code
   * ( get-learned-literals :type )
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param type The type of learned literals to return
   * @return The list of learned literals.
   */
  public Term[] getLearnedLiterals(LearnedLitType type)
  {
    long[] retPointers = getLearnedLiterals(pointer, type.getValue());
    return Utils.getTerms(retPointers);
  }

  private native long[] getLearnedLiterals(long pointer, int type);

  /**
   * Get the list of asserted formulas.
   *
   * SMT-LIB:
   * {@code
   * ( get-assertions )
   * }
   *
   * @return The list of asserted formulas.
   */
  public Term[] getAssertions()
  {
    long[] retPointers = getAssertions(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getAssertions(long pointer);

  /**
   * Get info from the solver.
   * SMT-LIB: {@code ( get-info <info_flag> ) }
   * @return The info.
   */
  public String getInfo(String flag)
  {
    return getInfo(pointer, flag);
  }

  private native String getInfo(long pointer, String flag);

  /**
   * Get the value of a given option.
   * SMT-LIB:
   * {@code
   * ( get-option <keyword> )
   * }
   * @param option The option for which the value is queried.
   * @return A string representation of the option value.
   */
  public String getOption(String option)
  {
    return getOption(pointer, option);
  }

  private native String getOption(long pointer, String option);

  /**
   * Get all option names that can be used with
   * {@link Solver#setOption(String, String)},
   * {@link Solver#getOption(String)} and
   * {@link Solver#getOptionInfo(String)}.
   * @return All option names.
   */
  public String[] getOptionNames()
  {
    return getOptionNames(pointer);
  }

  private native String[] getOptionNames(long pointer);

  /**
   * Get some information about the given option.
   *
   * Check the {@link OptionInfo} class for more details on which information
   * is available.
   *
   * @return Information about the given option.
   */
  public OptionInfo getOptionInfo(String option)
  {
    long optionPointer = getOptionInfo(pointer, option);
    return new OptionInfo(optionPointer);
  }

  private native long getOptionInfo(long pointer, String option);

  /**
   * Get the set of unsat ("failed") assumptions.
   *
   * SMT-LIB:
   * {@code
   * ( get-unsat-assumptions )
   * }
   *
   * Requires to enable option {@code produce-unsat-assumptions}.
   *
   * @return The set of unsat assumptions.
   */
  public Term[] getUnsatAssumptions()
  {
    long[] retPointers = getUnsatAssumptions(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getUnsatAssumptions(long pointer);

  /**
   * Get the unsatisfiable core.
   * SMT-LIB:
   * {@code
   * (get-unsat-core)
   * }
   * Requires to enable option {@code produce-unsat-cores}.
   *
   * @api.note In contrast to SMT-LIB, cvc5's API does not distinguish between
   *           named and unnamed assertions when producing an unsatisfiable
   *           core. Additionally, the API allows this option to be called after
   *           a check with assumptions. A subset of those assumptions may be
   *           included in the unsatisfiable core returned by this method.
   *
   * @return A set of terms representing the unsatisfiable core.
   */
  public Term[] getUnsatCore()
  {
    long[] retPointers = getUnsatCore(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getUnsatCore(long pointer);

  /**
   * Get a difficulty estimate for an asserted formula. This method is
   * intended to be called immediately after any response to a checkSat.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A map from (a subset of) the input assertions to a real value that.
   * is an estimate of how difficult each assertion was to solve. Unmentioned
   * assertions can be assumed to have zero difficulty.
   */
  public Map<Term, Term> getDifficulty()
  {
    Map<Long, Long> map = getDifficulty(pointer);
    Map<Term, Term> ret = new HashMap<>();
    for (Map.Entry<Long, Long> entry : map.entrySet())
    {
      Term key = new Term(entry.getKey());
      Term value = new Term(entry.getValue());
      ret.put(key, value);
    }
    return ret;
  }

  private native Map<Long, Long> getDifficulty(long pointer);

  /**
   * Get a timeout core, which computes a subset of the current assertions that
   * cause a timeout. Note it does not require being proceeded by a call to
   * checkSat.
   *
   * SMT-LIB:
   * {@code
   * (get-timeout-core)
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The result of the timeout core computation. This is a pair
   * containing a result and a list of formulas. If the result is unknown
   * and the reason is timeout, then the list of formulas correspond to a
   * subset of the current assertions that cause a timeout in the specified
   * time {@code timeout-core-timeout}.
   * If the result is unsat, then the list of formulas correspond to an
   * unsat core for the current assertions. Otherwise, the result is sat,
   * indicating that the current assertions are satisfiable, and
   * the list of formulas is empty.
   *
   * This method may make multiple checks for satisfiability internally, each
   * limited by the timeout value given by {@code timeout-core-timeout}.
   */
  public Pair<Result, Term[]> getTimeoutCore()
  {
    Pair<Long, long[]> pair = getTimeoutCore(pointer);
    Result result = new Result(pair.first);
    Term[] terms = Utils.getTerms(pair.second);
    Pair<Result, Term[]> ret = new Pair<>(result, terms);
    return ret;
  }

  private native Pair<Long, long[]> getTimeoutCore(long pointer);

  /**
   * Get refutation proof for the most recent call to checkSat.
   *
   * SMT-LIB:
   * {@code
   * ( get-proof )
   * }
   *
   * Requires to enable option {@code produce-proofs}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A string representing the proof. This is impacted by the value of
   * proof-format-mode.
   */
  public String getProof()
  {
    return getProof(pointer);
  }

  private native String getProof(long pointer);

  /**
   * Get a proof associated with the most recent call to checkSat.
   *
   * SMT-LIB:
   * {@code
   * ( get-proof :c)
   * }
   *
   * Requires to enable option {@code produce-proofs}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param c The component of the proof to return
   * @return A string representing the proof. This is equivalent to getProof
   * when c is PROOF_COMPONENT_FULL.
   */
  public String getProof(ProofComponent c)
  {
    return getProof(pointer, c.getValue());
  }

  private native String getProof(long pointer, int c);

  /**
   * Get the value of the given term in the current model.
   *
   * SMT-LIB:
   * {@code
   * ( get-value ( <term> ) )
   * }
   *
   * @param term The term for which the value is queried.
   * @return The value of the given term.
   */
  public Term getValue(Term term)
  {
    long termPointer = getValue(pointer, term.getPointer());
    return new Term(termPointer);
  }

  private native long getValue(long pointer, long termPointer);

  /**
   * Get the values of the given terms in the current model.
   *
   * SMT-LIB:
   * {@code
   * ( get-value ( <term>+ ) )
   * }
   *
   * @param terms The terms for which the value is queried.
   * @return The values of the given terms.
   */
  public Term[] getValue(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    long[] retPointers = getValue(pointer, pointers);
    return Utils.getTerms(retPointers);
  }

  private native long[] getValue(long pointer, long[] termPointers);

  /**
   * Get the domain elements of uninterpreted sort s in the current model.
   *
   * The current model interprets {@code s} as the finite sort whose domain
   * elements are given in the return value of this method.
   *
   * @param s The uninterpreted sort in question.
   * @return The domain elements of {@code s} in the current model.
   */
  public Term[] getModelDomainElements(Sort s)
  {
    long[] pointers = getModelDomainElements(pointer, s.getPointer());
    return Utils.getTerms(pointers);
  }

  private native long[] getModelDomainElements(long pointer, long sortPointer);

  /**
   * This returns false if the model value of free constant {@code v} was not
   * essential for showing the satisfiability of the last call to
   * {@link Solver#checkSat()} using the current model. This method will only
   * return false (for any {@code v}) if the option {@code model-cores} has
   * been set.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param v The term in question.
   * @return True if v is a model core symbol.
   */
  public boolean isModelCoreSymbol(Term v)
  {
    return isModelCoreSymbol(pointer, v.getPointer());
  }

  private native boolean isModelCoreSymbol(long pointer, long termPointer);

  /**
   * Get the model
   *
   * SMT-LIB:
   * {@code
   * ( get-model )
   * }
   *
   * Requires to enable option {@code produce-models}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param sorts The list of uninterpreted sorts that should be printed in the.
   *              model.
   * @param vars The list of free constants that should be printed in the.
   *             model. A subset of these may be printed based on
   *             {@link Solver#isModelCoreSymbol(Term)}.
   * @return A string representing the model.
   */
  public String getModel(Sort[] sorts, Term[] vars)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long[] varPointers = Utils.getPointers(vars);
    return getModel(pointer, sortPointers, varPointers);
  }

  private native String getModel(long pointer, long[] sortPointers, long[] varPointers);

  /**
   * Do quantifier elimination.
   *
   * SMT-LIB:
   * {@code
   * ( get-qe <q> )
   * }
   *
   * Quantifier Elimination is is only complete for logics such as LRA,
   * LIA and BV.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param q A quantified formula of the form:
   *          {@code Q x1...xn. P( x1...xn, y1...yn )}
   *          where {@code P( x1...xn, y1...yn )} is a quantifier-free formula.
   * @return A formula {@code ret} such that, given the current set of formulas
   *         {@code A} asserted to this solver:
   *         - {@code ( A && q )} and {@code ( A && ret )} are equivalent
   *         - {@code ret} is quantifier-free formula containing only free
   *           variables in {@code y1...yn}.
   */
  public Term getQuantifierElimination(Term q)
  {
    long termPointer = getQuantifierElimination(pointer, q.getPointer());
    return new Term(termPointer);
  }

  private native long getQuantifierElimination(long pointer, long qPointer);

  /**
   * Do partial quantifier elimination, which can be used for incrementally
   * computing the result of a quantifier elimination.
   *
   * SMT-LIB:
   * {@code
   * ( get-qe-disjunct <q> )
   * }
   *
   * Quantifier Elimination is is only complete for logics such as LRA,
   * LIA and BV.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param q A quantified formula of the form:
   *          {@code Q x1...xn. P( x1...xn, y1...yn )}
   *          where {@code P( x1...xn, y1...yn )} is a quantifier-free formula.
   * @return A formula ret such that, given the current set of formulas A
   *         asserted to this solver:
   *           - {@code (A ^ q) => (A ^ ret)} if {@code Q} is forall or
   *             {@code (A ^ ret) => (A ^ q)} if {@code Q} is exists,
   *           - ret is quantifier-free formula containing only free variables
   *             in {@code y1...yn},
   *           - If Q is exists, let {@code A && Q_n} be the formula
   *               {@code A && ~(ret && Q_1) && ... && ~(ret && Q_n)}
   *             where for each {@code i=1,...n}, formula {@code ret && Q_i}
   *             is the result of calling
   *             {@link Solver#getQuantifierEliminationDisjunct(Term)}
   *             for {@code q} with the set of assertions
   *             {@code A && Q_{i-1}}. Similarly, if {@code Q} is forall, then
   *             let {@code A && Q_n} be
   *             {@code A && (ret && Q_1) && ... && (ret&& Q_n) }
   *             where {@code ret && Q_i} is the same as above. In either case,
   *             we have that {@code ret && Q_j} will eventually be true or
   *             false, for some finite {@code j}.
   */
  public Term getQuantifierEliminationDisjunct(Term q)
  {
    long termPointer = getQuantifierEliminationDisjunct(pointer, q.getPointer());
    return new Term(termPointer);
  }

  private native long getQuantifierEliminationDisjunct(long pointer, long qPointer);

  /**
   * When using separation logic, this sets the location sort and the
   * datatype sort to the given ones. This method should be invoked exactly
   * once, before any separation logic constraints are provided.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param locSort The location sort of the heap.
   * @param dataSort The data sort of the heap.
   */
  public void declareSepHeap(Sort locSort, Sort dataSort)
  {
    declareSepHeap(pointer, locSort.getPointer(), dataSort.getPointer());
  }

  private native void declareSepHeap(long pointer, long locSortPointer, long dataSortPointer);

  /**
   * When using separation logic, obtain the term for the heap.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The term for the heap.
   */
  public Term getValueSepHeap()
  {
    long termPointer = getValueSepHeap(pointer);
    return new Term(termPointer);
  }

  private native long getValueSepHeap(long pointer);

  /**
   * When using separation logic, obtain the term for nil.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The term for nil.
   */
  public Term getValueSepNil()
  {
    long termPointer = getValueSepNil(pointer);
    return new Term(termPointer);
  }

  private native long getValueSepNil(long pointer);

  /**
   * Declare a symbolic pool of terms with the given initial value.
   *
   * SMT-LIB:
   * {@code
   * ( declare-pool <symbol> <sort> ( <term>* ) )
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param symbol The name of the pool.
   * @param sort The sort of the elements of the pool.
   * @param initValue The initial value of the pool.
   */
  public Term declarePool(String symbol, Sort sort, Term[] initValue)
  {
    long[] termPointers = Utils.getPointers(initValue);
    long termPointer = declarePool(pointer, symbol, sort.getPointer(), termPointers);
    return new Term(termPointer);
  }

  private native long declarePool(
      long pointer, String symbol, long sortPointer, long[] termPointers);

  /**
   * Declare an oracle function with reference to an implementation.
   *
   * Oracle functions have a different semantics with respect to ordinary
   * declared functions. In particular, for an input to be satisfiable,
   * its oracle functions are implicitly universally quantified.
   *
   * This method is used in part for implementing this command:
   *
   * {@code
   * (declare-oracle-fun <sym> (<sort>*) <sort> <sym>)
   * }
   *
   *
   * In particular, the above command is implemented by constructing a
   * function over terms that wraps a call to binary sym via a text interface.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param symbol The name of the oracle
   * @param sorts The sorts of the parameters to this function
   * @param sort The sort of the return value of this function
   * @param oracle An object that implements the oracle interface.
   * @return The oracle function
   */
  public Term declareOracleFun(String symbol, Sort[] sorts, Sort sort, IOracle oracle)
  {
    oracles.add(oracle);
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareOracleFun(pointer, symbol, sortPointers, sort.getPointer(), oracle);
    return new Term(termPointer);
  }

  private native long declareOracleFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer, IOracle oracle);

  /**
   * Pop a level from the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   *
   * @throws CVC5ApiException
   */
  public void pop() throws CVC5ApiException
  {
    pop(1);
  }

  /**
   * Pop (a) level(s) from the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   *
   * @param nscopes The number of levels to pop.
   * @throws CVC5ApiException
   */
  public void pop(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    pop(pointer, nscopes);
  }

  private native void pop(long pointer, int nscopes);

  /**
   * Get an interpolant
   *
   * SMT-LIB:
   * {@code
   * ( get-interpolant <conj> )
   * }
   *
   * Requires option {@code produce-interpolants} to be set to a mode different
   * from {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return A Term I such that {@code A->I} and {@code I->B} are valid, where
   *         {@code A} is the current set of assertions and {@code B} is given
   *         in the input by {@code conj}, or the null term if such a term
   *         cannot be found.
   */
  public Term getInterpolant(Term conj)
  {
    long interpolPtr = getInterpolant(pointer, conj.getPointer());
    return new Term(interpolPtr);
  }

  private native long getInterpolant(long pointer, long conjPointer);

  /**
   * Get an interpolant
   *
   * SMT-LIB:
   * {@code
   * ( get-interpolant <conj> <g> )
   * }
   *
   * Requires option {@code produce-interpolants} to be set to a mode different
   * from {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the interpolant I.
   * @return A Term I such that {@code A->I} and {@code I->B} are valid, where
   *         {@code A} is the current set of assertions and {@code B} is given
   *         in the input by {@code conj}, or the null term if such a term
   *         cannot be found.
   */
  public Term getInterpolant(Term conj, Grammar grammar)
  {
    long interpolPtr = getInterpolant(pointer, conj.getPointer(), grammar.getPointer());
    return new Term(interpolPtr);
  }

  private native long getInterpolant(long pointer, long conjPointer, long grammarPointer);

  /**
   * Get the next interpolant.
   *
   * Can only be called immediately after a successful call to
   * {@code get-interpolant} or {@code get-interpolant-next}. Is guaranteed to
   * produce a syntactically different interpolant wrt the last returned
   * interpolant if successful.
   *
   * SMT-LIB:
   * {@code
   *     (get-interpolant-next)
   * }
   *
   * Requires to enable incremental mode, and option
   * {@code produce-interpolants} to be set to a mode different from
   * {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A Term I such that {@code A->I} and {@code I->B} are valid,
   *         where {@code A} is the current set of assertions and {@code B}
   *         is given in the input by conj on the last call to getInterpolant,
   *         or the null term if such a term cannot be found.
   */
  public Term getInterpolantNext()
  {
    long interpolPtr = getInterpolantNext(pointer);
    return new Term(interpolPtr);
  }

  private native long getInterpolantNext(long pointer);

  /**
   * Get an abduct.
   *
   * SMT-LIB:
   * {@code
   * ( get-abduct <conj> )
   * }
   * Requires enabling option {@code produce-abducts}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return A term {@code C} such that {@code A && C} is satisfiable, and
   *         {@code A && ~B && C} is unsatisfiable, where {@code A} is the
   *         current set of assertions and {@code B} is given in the input by
   *         {@code conj}, or the null term if such a term cannot be found.
   */
  public Term getAbduct(Term conj)
  {
    long abdPtr = getAbduct(pointer, conj.getPointer());
    return new Term(abdPtr);
  }

  private native long getAbduct(long pointer, long conjPointer);
  /**
   * Get an abduct.
   *
   * SMT-LIB:
   * {@code
   * ( get-abduct <conj> <g> )
   * }
   *
   * Requires enabling option {@code produce-abducts}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the abduct {@code C}.
   * @return A term {@code C} such that {@code A && C} is satisfiable, and
   *         {@code A && ~B && C} is unsatisfiable, where {@code A} is the
   *         current set of assertions and {@code B} is given in the input by
   *         {@code conj}, or the null term if such a term cannot be found.
   */
  public Term getAbduct(Term conj, Grammar grammar)
  {
    long abdPtr = getAbduct(pointer, conj.getPointer(), grammar.getPointer());
    return new Term(abdPtr);
  }

  private native long getAbduct(long pointer, long conjPointer, long grammarPointer);

  /**
   * Get the next abduct. Can only be called immediately after a successful
   * call to get-abduct or get-abduct-next. Is guaranteed to produce a
   * syntactically different abduct wrt the last returned abduct if successful.
   * SMT-LIB:
   * {@code
   * ( get-abduct-next )
   * }
   * Requires enabling incremental mode and option {@code produce-abducts}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A term C such that A^C is satisfiable, and A^~B^C is.
   *         unsatisfiable, where A is the current set of assertions and B is
   *         given in the input by conj in the last call to getAbduct, or the
   *         null term if such a term cannot be found.
   */
  public Term getAbductNext()
  {
    long abdPtr = getAbductNext(pointer);
    return new Term(abdPtr);
  }

  private native long getAbductNext(long pointer);

  /**
   * Block the current model.
   *
   * Can be called only if immediately preceded by a SAT or INVALID query.
   *
   * SMT-LIB:
   * {@code
   * ( block-model )
   * }
   *
   * Requires enabling option {@code produce-models}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param mode The mode to use for blocking.
   */
  public void blockModel(BlockModelsMode mode)
  {
    blockModel(pointer, mode.getValue());
  }

  private native void blockModel(long pointer, int modeValue);

  /**
   * Block the current model values of (at least) the values in terms.
   *
   * Can be called only if immediately preceded by a SAT query.
   *
   * SMT-LIB:
   * {@code
   * ( block-model-values ( <terms>+ ) )
   * }
   *
   * Requires enabling option {@code produce-models}.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public void blockModelValues(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    blockModelValues(pointer, pointers);
  }

  private native void blockModelValues(long pointer, long[] termPointers);

  /**
   * Return a string that contains information about all instantiations made by
   * the quantifiers module.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public String getInstantiations()
  {
    return getInstantiations(pointer);
  }

  private native String getInstantiations(long pointer);

  /**
   * Push a level to the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( push <numeral> )
   * }
   *
   * @throws CVC5ApiException
   */
  public void push() throws CVC5ApiException
  {
    push(1);
  }

  /**
   * Push (a) level(s) to the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( push <numeral> )
   * }
   *
   * @param nscopes The number of levels to push.
   * @throws CVC5ApiException
   */
  public void push(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    push(pointer, nscopes);
  }

  private native void push(long pointer, int nscopes);

  /**
   * Remove all assertions.
   *
   * SMT-LIB:
   * {@code
   * ( reset-assertions )
   * }
   */
  public void resetAssertions()
  {
    resetAssertions(pointer);
  }

  private native void resetAssertions(long pointer);

  /**
   * Set info.
   *
   * SMT-LIB:
   * {@code
   * ( set-info <attribute> )
   * }
   *
   * @param keyword The info flag.
   * @param value The value of the info flag.
   * @throws CVC5ApiException
   */
  public void setInfo(String keyword, String value) throws CVC5ApiException
  {
    setInfo(pointer, keyword, value);
  }

  private native void setInfo(long pointer, String keyword, String value) throws CVC5ApiException;

  /**
   * Set logic.
   *
   * SMT-LIB:
   * {@code
   * ( set-logic <symbol> )
   * }
   *
   * @param logic The logic to set.
   * @throws CVC5ApiException
   */
  public void setLogic(String logic) throws CVC5ApiException
  {
    setLogic(pointer, logic);
  }

  private native void setLogic(long pointer, String logic) throws CVC5ApiException;

  /**
   * Set option.
   *
   * SMT-LIB:
   * {@code
   *   ( set-option <option> )
   * }
   *
   * @param option The option name.
   * @param value The option value.
   */
  public void setOption(String option, String value)
  {
    setOption(pointer, option, value);
  }

  private native void setOption(long pointer, String option, String value);

  /**
   * Append {@code symbol} to the current list of universal variables.
   *
   * SyGuS v2:
   * {@code
   *   ( declare-var <symbol> <sort> )
   * }
   *
   * @param sort The sort of the universal variable.
   * @param symbol The name of the universal variable.
   * @return The universal variable.
   */
  public Term declareSygusVar(String symbol, Sort sort)
  {
    long termPointer = declareSygusVar(pointer, symbol, sort.getPointer());
    return new Term(termPointer);
  }

  private native long declareSygusVar(long pointer, String symbol, long sortPointer);

  /**
   * Create a Sygus grammar.
   *
   * The first non-terminal is treated as the starting non-terminal, so the
   * order of non-terminals matters.
   *
   * @param boundVars The parameters to corresponding synth-fun/synth-inv.
   * @param ntSymbols The pre-declaration of the non-terminal symbols.
   * @return The grammar.
   */
  public Grammar mkGrammar(Term[] boundVars, Term[] ntSymbols)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long[] ntSymbolPointers = Utils.getPointers(ntSymbols);
    long grammarPointer = mkGrammar(pointer, boundVarPointers, ntSymbolPointers);
    return new Grammar(grammarPointer);
  }

  private native long mkGrammar(long pointer, long[] boundVarPointers, long[] ntSymbolPointers);

  /**
   * Synthesize n-ary function.
   *
   * SyGuS v2:
   * {@code
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @return The function.
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthFun(pointer, symbol, boundVarPointers, sort.getPointer());
    return new Term(termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer);

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   *
   * SyGuS v2:
   * {@code
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )
   * }
   *
   * @param symbol The name of the function.
   * @param boundVars The parameters to this function.
   * @param sort The sort of the return value of this function.
   * @param grammar The syntactic constraints.
   * @return The function.
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort, Grammar grammar)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        synthFun(pointer, symbol, boundVarPointers, sort.getPointer(), grammar.getPointer());
    return new Term(termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer, long grammarPointer);

  /**
   * Add a forumla to the set of Sygus constraints.
   *
   * SyGuS v2:
   * {@code
   *   ( constraint <term> )
   * }
   *
   * @param term The formula to add as a constraint.
   */
  public void addSygusConstraint(Term term)
  {
    addSygusConstraint(pointer, term.getPointer());
  }

  private native void addSygusConstraint(long pointer, long termPointer);

  /**
   * Get the list of sygus constraints.
   *
   * @return The list of sygus constraints.
   */
  public Term[] getSygusConstraints()
  {
    long[] retPointers = getSygusConstraints(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getSygusConstraints(long pointer);

  /**
   * Add a forumla to the set of Sygus assumptions.
   *
   * SyGuS v2:
   * {@code
   *   ( assume <term> )
   * }
   *
   * @param term The formula to add as an assumption.
   */
  public void addSygusAssume(Term term)
  {
    addSygusAssume(pointer, term.getPointer());
  }

  private native void addSygusAssume(long pointer, long termPointer);

  /**
   * Get the list of sygus assumptions.
   *
   * @return The list of sygus assumptions.
   */
  public Term[] getSygusAssumptions()
  {
    long[] retPointers = getSygusAssumptions(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getSygusAssumptions(long pointer);

  /**
   * Add a set of Sygus constraints to the current state that correspond to an
   * invariant synthesis problem.
   *
   * SyGuS v2:
   * {@code
   *   ( inv-constraint <inv> <pre> <trans> <post> )
   * }
   *
   * @param inv The function-to-synthesize.
   * @param pre The pre-condition.
   * @param trans The transition relation.
   * @param post The post-condition.
   */
  public void addSygusInvConstraint(Term inv, Term pre, Term trans, Term post)
  {
    addSygusInvConstraint(
        pointer, inv.getPointer(), pre.getPointer(), trans.getPointer(), post.getPointer());
  }

  private native void addSygusInvConstraint(
      long pointer, long invPointer, long prePointer, long transPointer, long postPointer);

  /**
   * Try to find a solution for the synthesis conjecture corresponding to the
   * current list of functions-to-synthesize, universal variables and
   * constraints.
   *
   * SyGuS v2:
   * {@code
   *   ( check-synth )
   * }
   *
   * @return The result of the check, which is "solution" if the check found a.
   *         solution in which case solutions are available via
   *         getSynthSolutions, "no solution" if it was determined there is no
   *         solution, or "unknown" otherwise.
   */
  public SynthResult checkSynth()
  {
    long resultPointer = checkSynth(pointer);
    return new SynthResult(resultPointer);
  }

  private native long checkSynth(long pointer);

  /**
   * Try to find a next solution for the synthesis conjecture corresponding to
   * the current list of functions-to-synthesize, universal variables and
   * constraints. Must be called immediately after a successful call to
   * {@code check-synth} or {@code check-synth-next}.
   *
   * @api.note Requires incremental mode.
   *
   * SyGuS v2:
   * {@code
   *   ( check-synth-next )
   * }
   *
   * @return The result of the check, which is "solution" if the check found a
   *         solution in which case solutions are available via
   *         getSynthSolutions, "no solution" if it was determined there is no
   *         solution, or "unknown" otherwise.
   */
  public SynthResult checkSynthNext()
  {
    long resultPointer = checkSynthNext(pointer);
    return new SynthResult(resultPointer);
  }

  private native long checkSynthNext(long pointer);

  /**
   * Get the synthesis solution of the given term.
   *
   * This method should be called immediately after the solver answers unsat
   * for sygus input.
   *
   * @param term The term for which the synthesis solution is queried.
   * @return The synthesis solution of the given term.
   */
  public Term getSynthSolution(Term term)
  {
    long termPointer = getSynthSolution(pointer, term.getPointer());
    return new Term(termPointer);
  }

  private native long getSynthSolution(long pointer, long termPointer);

  /**
   * Get the synthesis solutions of the given terms.
   *
   * This method should be called immediately after the solver answers unsat
   * for sygus input.
   *
   * @param terms The terms for which the synthesis solutions is queried.
   * @return The synthesis solutions of the given terms.
   */
  public Term[] getSynthSolutions(Term[] terms)
  {
    long[] termPointers = Utils.getPointers(terms);
    long[] retPointers = getSynthSolutions(pointer, termPointers);
    return Utils.getTerms(retPointers);
  }

  private native long[] getSynthSolutions(long pointer, long[] termPointers);

  /**
   * Returns a snapshot of the current state of the statistic values of this
   * solver. The returned object is completely decoupled from the solver and
   * will not change when the solver is used again.
   */
  public Statistics getStatistics()
  {
    long statisticsPointer = getStatistics(pointer);
    return new Statistics(statisticsPointer);
  }

  private native long getStatistics(long pointer);

  /**
   * Get a string representation of the version of this solver.
   * @return The version string.
   */
  public String getVersion()
  {
    return getVersion(pointer);
  }

  private native String getVersion(long pointer);
}
