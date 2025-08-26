/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
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

import io.github.cvc5.TermManager;
import io.github.cvc5.modes.BlockModelsMode;
import io.github.cvc5.modes.FindSynthTarget;
import io.github.cvc5.modes.LearnedLitType;
import io.github.cvc5.modes.ProofComponent;
import io.github.cvc5.modes.ProofFormat;
import java.io.IOException;
import java.util.*;

/**
 * A cvc5 solver.
 */
public class Solver extends AbstractPointer
{
  private TermManager d_tm;

  static
  {
    Utils.loadLibraries();
  }

  // store IOracle objects
  List<IOracle> oracles = new ArrayList<>();

  /**
   * Create solver instance.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link Solver#Solver(TermManager)}.
   * It will be removed in a future release.
   */
  @Deprecated
  public Solver()
  {
    this(new TermManager());
  }

  /**
   * Create solver instance.
   * @param d_tm The associated term manager.
   */
  public Solver(TermManager d_tm)
  {
    super(Solver.newSolver(d_tm.getPointer()));
    this.d_tm = d_tm;
  }
  private static native long newSolver(long tmPointer);

  /**
   * This is an internal constructor intended to be used only
   * inside cvc5 package
   * @param pointer the cpp pointer to Solver
   */
  Solver(long solverPointer)
  {
    super(solverPointer);
  }

  protected native void deletePointer(long pointer);

  protected String toString(long pointer)
  {
    throw new UnsupportedOperationException("Solver.toString() is not supported in the cpp api");
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
    Solver solver = (Solver) s;
    if (this.pointer == solver.pointer)
    {
      return true;
    }
    return false;
  }

  /**
   * Get the associated term manager instance
   * @return The term manager.
   */
  public TermManager getTermManager()
  {
    return new TermManager(getTermManager(pointer));
  }
  private native long getTermManager(long pointer);

  /* .................................................................... */
  /* Sorts Handling                                                       */
  /* .................................................................... */

  /**
   * Get the Boolean sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#getBooleanSort()}.
   * It will be removed in a future release.
   *
   * @return Sort Boolean.
   */
  @Deprecated
  public Sort getBooleanSort()
  {
    return d_tm.getBooleanSort();
  }

  /**
   * Get the integer sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#getIntegerSort()}.
   * It will be removed in a future release.
   *
   * @return Sort Integer.
   */
  @Deprecated
  public Sort getIntegerSort()
  {
    return d_tm.getIntegerSort();
  }

  /**
   * Get the real sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#getRealSort()}.
   * It will be removed in a future release.
   *
   * @return Sort Real.
   */
  @Deprecated
  public Sort getRealSort()
  {
    return d_tm.getRealSort();
  }

  /**
   * Get the regular expression sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#getRegExpSort()}.
   * It will be removed in a future release.
   *
   * @return Sort RegExp.
   */
  @Deprecated
  public Sort getRegExpSort()
  {
    return d_tm.getRegExpSort();
  }

  /**
   * Get the floating-point rounding mode sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#getRoundingModeSort()}.
   * It will be removed in a future release.
   *
   * @return Sort RoundingMode.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort getRoundingModeSort() throws CVC5ApiException
  {
    return d_tm.getRoundingModeSort();
  }

  /**
   * Get the string sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#getStringSort()}.
   * It will be removed in a future release.
   *
   * @return Sort String.
   */
  @Deprecated
  public Sort getStringSort()
  {
    return d_tm.getStringSort();
  }

  /**
   * Create an array sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkArraySort(Sort, Sort)}.
   * It will be removed in a future release.
   *
   * @param indexSort The array index sort.
   * @param elemSort The array element sort.
   * @return The array sort.
   */
  @Deprecated
  public Sort mkArraySort(Sort indexSort, Sort elemSort)
  {
    return d_tm.mkArraySort(indexSort, elemSort);
  }

  /**
   * Create a bit-vector sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkBitVectorSort(int)}.
   * It will be removed in a future release.
   *
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkBitVectorSort(int size) throws CVC5ApiException
  {
    return d_tm.mkBitVectorSort(size);
  }

  /**
   * Create a finite field sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFiniteFieldSort(String, int)}.
   * It will be removed in a future release.
   *
   * @param size The size of the finite field sort.
   * @param base The base of the string representation.
   * @return The finite field sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkFiniteFieldSort(String size, int base) throws CVC5ApiException
  {
    return d_tm.mkFiniteFieldSort(size, base);
  }

  /**
   * Create a floating-point sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPointSort(int, int)}.
   * It will be removed in a future release.
   *
   * @param exp The bit-width of the exponent of the floating-point sort.
   * @param sig The bit-width of the significand of the floating-point sort.
   * @return The floating-point sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkFloatingPointSort(int exp, int sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPointSort(exp, sig);
  }

  /**
   * Create a datatype sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeSort(DatatypeDecl)}.
   * It will be removed in a future release.
   *
   * @param dtypedecl The datatype declaration from which the sort is created.
   * @return The datatype sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkDatatypeSort(DatatypeDecl dtypedecl) throws CVC5ApiException
  {
    return d_tm.mkDatatypeSort(dtypedecl);
  }

  /**
   * Create a vector of datatype sorts.
   *
   * The names of the datatype declarations must be distinct.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeSorts(DatatypeDecl[])}.
   * It will be removed in a future release.
   *
   * @param dtypedecls The datatype declarations from which the sort is created.
   * @return The datatype sorts.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort[] mkDatatypeSorts(DatatypeDecl[] dtypedecls) throws CVC5ApiException
  {
    return d_tm.mkDatatypeSorts(dtypedecls);
  }

  /**
   * Create function sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFunctionSort(Sort, Sort)}.
   * It will be removed in a future release.
   *
   * @param domain The sort of the fuction argument.
   * @param codomain The sort of the function return value.
   * @return The function sort.
   */
  @Deprecated
  public Sort mkFunctionSort(Sort domain, Sort codomain)
  {
    return d_tm.mkFunctionSort(domain, codomain);
  }

  /**
   * Create function sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFunctionSort(Sort[], Sort)}.
   * It will be removed in a future release.
   *
   * @param sorts The sort of the function arguments.
   * @param codomain The sort of the function return value.
   * @return The function sort.
   */
  @Deprecated
  public Sort mkFunctionSort(Sort[] sorts, Sort codomain)
  {
    return d_tm.mkFunctionSort(sorts, codomain);
  }

  /**
   * Create a sort parameter.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkParamSort(String)}.
   * It will be removed in a future release.
   *
   * @param symbol The name of the sort.
   * @return The sort parameter.
   */
  @Deprecated
  public Sort mkParamSort(String symbol)
  {
    return d_tm.mkParamSort(symbol);
  }

  /**
   * Create a sort parameter.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkParamSort()}.
   * It will be removed in a future release.
   *
   * @return The sort parameter.
   */
  @Deprecated
  public Sort mkParamSort()
  {
    return d_tm.mkParamSort();
  }

  /**
   * Create a predicate sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkPredicateSort(Sort[])}.
   * It will be removed in a future release.
   *
   * @param sorts The list of sorts of the predicate.
   * @return The predicate sort.
   */
  @Deprecated
  public Sort mkPredicateSort(Sort[] sorts)
  {
    return d_tm.mkPredicateSort(sorts);
  }

  /**
   * Create a record sort
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkRecordSort(Pair[])}.
   * It will be removed in a future release.
   *
   * @param fields The list of fields of the record.
   * @return The record sort.
   */
  @Deprecated
  public Sort mkRecordSort(Pair<String, Sort>[] fields)
  {
    return d_tm.mkRecordSort(fields);
  }

  /**
   * Create a set sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkSetSort(Sort)}.
   * It will be removed in a future release.
   *
   * @param elemSort The sort of the set elements.
   * @return The set sort.
   */
  @Deprecated
  public Sort mkSetSort(Sort elemSort)
  {
    return d_tm.mkSetSort(elemSort);
  }

  /**
   * Create a bag sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkBagSort(Sort)}.
   * It will be removed in a future release.
   *
   * @param elemSort The sort of the bag elements.
   * @return The bag sort.
   */
  @Deprecated
  public Sort mkBagSort(Sort elemSort)
  {
    return d_tm.mkBagSort(elemSort);
  }

  /**
   * Create a sequence sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkSequenceSort(Sort)}.
   * It will be removed in a future release.
   *
   * @param elemSort The sort of the sequence elements.
   * @return The sequence sort.
   */
  @Deprecated
  public Sort mkSequenceSort(Sort elemSort)
  {
    return d_tm.mkSequenceSort(elemSort);
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
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkAbstractSort(SortKind)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the abstract sort
   * @return The abstract sort.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  @Deprecated
  public Sort mkAbstractSort(SortKind kind)
  {
    return d_tm.mkAbstractSort(kind);
  }

  /**
   * Create an uninterpreted sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUninterpretedSort(String)}.
   * It will be removed in a future release.
   *
   * @param symbol The name of the sort.
   * @return The uninterpreted sort.
   */
  @Deprecated
  public Sort mkUninterpretedSort(String symbol)
  {
    return d_tm.mkUninterpretedSort(symbol);
  }

  /**
   * Create an uninterpreted sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUninterpretedSort()}.
   * It will be removed in a future release.
   *
   * @return The uninterpreted sort.
   */
  @Deprecated
  public Sort mkUninterpretedSort()
  {
    return d_tm.mkUninterpretedSort();
  }

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive parametric datatypes.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUnresolvedDatatypeSort(String, int)}.
   * It will be removed in a future release.
   *
   * @param symbol The symbol of the sort.
   * @param arity The number of sort parameters of the sort.
   * @return The unresolved sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkUnresolvedDatatypeSort(String symbol, int arity) throws CVC5ApiException
  {
    return d_tm.mkUnresolvedDatatypeSort(symbol, arity);
  }

  /**
   * Create an unresolved datatype sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive datatypes without sort parameters.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUnresolvedDatatypeSort(String)}.
   * It will be removed in a future release.
   *
   * @param symbol The symbol of the sort.
   * @return The unresolved sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
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
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUninterpretedSortConstructorSort(int, String)}.
   * It will be removed in a future release.
   *
   * @param arity The arity of the sort (must be &gt; 0)
   * @param symbol The symbol of the sort.
   * @return The sort constructor sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkUninterpretedSortConstructorSort(int arity, String symbol) throws CVC5ApiException
  {
    return d_tm.mkUninterpretedSortConstructorSort(arity, symbol);
  }

  /**
   * Create a sort constructor sort.
   *
   * An uninterpreted sort constructor is an uninterpreted sort with
   * arity &gt; 0.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUninterpretedSortConstructorSort(int)}.
   * It will be removed in a future release.
   *
   * @param arity The arity of the sort (must be &gt; 0)
   * @return The sort constructor sort.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Sort mkUninterpretedSortConstructorSort(int arity) throws CVC5ApiException
  {
    return d_tm.mkUninterpretedSortConstructorSort(arity);
  }

  /**
   * Create a tuple sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTupleSort(Sort[])}.
   * It will be removed in a future release.
   *
   * @param sorts Of the elements of the tuple.
   * @return The tuple sort.
   */
  @Deprecated
  public Sort mkTupleSort(Sort[] sorts)
  {
    return d_tm.mkTupleSort(sorts);
  }

  /**
   * Create a nullable sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableSort(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the element of the nullable.
   * @return The nullable sort.
   */
  @Deprecated
  public Sort mkNullableSort(Sort sort)
  {
    return d_tm.mkNullableSort(sort);
  }

  /* .................................................................... */
  /* Create Terms */
  /* .................................................................... */

  /**
   * Create 0-ary term of given kind.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Kind)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Kind kind)
  {
    return d_tm.mkTerm(kind);
  }

  /**
   * Create a unary term of given kind.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Kind, Term)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the term.
   * @param child The child of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Kind kind, Term child)
  {
    return d_tm.mkTerm(kind, child);
  }

  /**
   * Create binary term of given kind.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Kind, Term, Term)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the term.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Kind kind, Term child1, Term child2)
  {
    return d_tm.mkTerm(kind, child1, child2);
  }

  /**
   * Create ternary term of given kind.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Kind, Term, Term, Term)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the term.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @param child3 The third child of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Kind kind, Term child1, Term child2, Term child3)
  {
    return d_tm.mkTerm(kind, child1, child2, child3);
  }

  /**
   * Create n-ary term of given kind.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Kind, Term[])}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the term.
   * @param children The children of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Kind kind, Term[] children)
  {
    return d_tm.mkTerm(kind, children);
  }

  /**
   * Create nullary term of given kind from a given operator.
   * Create operators with mkOp().
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Op)}.
   * It will be removed in a future release.
   *
   * @param op The operator.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Op op)
  {
    return d_tm.mkTerm(op);
  }

  /**
   * Create unary term of given kind from a given operator.
   * Create operators with mkOp().
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Op, Term)}.
   * It will be removed in a future release.
   *
   * @param op The operator.
   * @param child The child of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Op op, Term child)
  {
    return d_tm.mkTerm(op, child);
  }

  /**
   * Create binary term of given kind from a given operator.
   * Create operators with mkOp().
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Op, Term, Term)}.
   * It will be removed in a future release.
   *
   * @param op The operator.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Op op, Term child1, Term child2)
  {
    return d_tm.mkTerm(op, child1, child2);
  }

  /**
   * Create ternary term of given kind from a given operator.
   * Create operators with mkOp().
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Op, Term, Term, Term)}.
   * It will be removed in a future release.
   *
   * @param op The operator.
   * @param child1 The first child of the term.
   * @param child2 The second child of the term.
   * @param child3 The third child of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Op op, Term child1, Term child2, Term child3)
  {
    return d_tm.mkTerm(op, child1, child2, child3);
  }

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTerm(Op, Term[])}.
   * It will be removed in a future release.
   *
   * @param op The operator.
   * @param children The children of the term.
   * @return The Term.
   */
  @Deprecated
  public Term mkTerm(Op op, Term[] children)
  {
    return d_tm.mkTerm(op, children);
  }

  /**
   * Create a tuple term. Terms are automatically converted if sorts are
   * compatible.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTuple(Term[])}.
   * It will be removed in a future release.
   *
   * @param terms The elements in the tuple.
   * @return The tuple Term.
   */
  @Deprecated
  public Term mkTuple(Term[] terms)
  {
    return d_tm.mkTuple(terms);
  }

  /**
   * Create a nullable some term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableSome(Term)}.
   * It will be removed in a future release.
   *
   * @param term The element value.
   * @return the Element value wrapped in some constructor.
   */
  @Deprecated
  public Term mkNullableSome(Term term)
  {
    return d_tm.mkNullableSome(term);
  }

  private native long mkNullableSome(long pointer, long termPointer);

  /**
   * Create a selector for nullable term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableVal(Term)}.
   * It will be removed in a future release.
   *
   * @param term A nullable term.
   * @return The element value of the nullable term.
   */
  @Deprecated
  public Term mkNullableVal(Term term)
  {
    return d_tm.mkNullableVal(term);
  }

  /**
   * Create a null tester for a nullable term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableIsNull(Term)}.
   * It will be removed in a future release.
   *
   * @param term A nullable term.
   * @return A tester whether term is null.
   */
  @Deprecated
  public Term mkNullableIsNull(Term term)
  {
    return d_tm.mkNullableIsNull(term);
  }

  /**
   * Create a some tester for a nullable term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableIsSome(Term)}.
   * It will be removed in a future release.
   *
   * @param term A nullable term.
   * @return A tester whether term is some.
   */
  @Deprecated
  public Term mkNullableIsSome(Term term)
  {
    return d_tm.mkNullableIsSome(term);
  }

  /**
   * Create a constant representing a null value of the given sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableNull(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the Nullable element.
   * @return The null constant.
   */
  @Deprecated
  public Term mkNullableNull(Sort sort)
  {
    return d_tm.mkNullableNull(sort);
  }

  /**
   * Create a term that lifts kind to nullable terms.
   *
   * Example:
   * If we have the term ((_ nullable.lift +) x y),
   * where x, y of type (Nullable Int), then
   * kind would be ADD, and args would be [x, y].
   * This function would return
   * (nullable.lift (lambda ((a Int) (b Int)) (+ a b)) x y)
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkNullableLift(Kind, Term[])}.
   * It will be removed in a future release.
   *
   * @param kind The lifted operator.
   * @param args The arguments of the lifted operator.
   * @return A term of Kind NULLABLE_LIFT where the first child
   * is a lambda expression, and the remaining children are
   * the original arguments.
   */
  @Deprecated
  public Term mkNullableLift(Kind kind, Term[] args)
  {
    return d_tm.mkNullableLift(kind, args);
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
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkOp(Kind)}.
   * It will be removed in a future release.
   *
   * @param kind The kind to wrap.
   * @return The operator.
   */
  @Deprecated
  public Op mkOp(Kind kind)
  {
    return d_tm.mkOp(kind);
  }

  /**
   * Create operator of kind:
   * <ul>
   *   <li>
   *     {@link Kind#DIVISIBLE} (to support arbitrary precision integers)
   *   </li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkOp(Kind, String)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the operator.
   * @param arg The string argument to this operator.
   * @return The operator.
   */
  @Deprecated
  public Op mkOp(Kind kind, String arg)
  {
    return d_tm.mkOp(kind, arg);
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
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkOp(Kind, int)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the operator.
   * @param arg The unsigned int argument to this operator.
   * @return The operator.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Op mkOp(Kind kind, int arg) throws CVC5ApiException
  {
    return d_tm.mkOp(kind, arg);
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
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkOp(Kind, int, int)}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the operator.
   * @param arg1 The first unsigned int argument to this operator.
   * @param arg2 The second unsigned int argument to this operator.
   * @return The operator.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Op mkOp(Kind kind, int arg1, int arg2) throws CVC5ApiException
  {
    return d_tm.mkOp(kind, arg1, arg2);
  }

  /**
   * Create operator of Kind:
   * <ul>
   *   <li>TUPLE_PROJECT</li>
   * </ul>
   * See enum {@link Kind} for a description of the parameters.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkOp(Kind, int[])}.
   * It will be removed in a future release.
   *
   * @param kind The kind of the operator.
   * @param args The arguments (indices) of the operator.
   * @return The operator.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Op mkOp(Kind kind, int[] args) throws CVC5ApiException
  {
    return d_tm.mkOp(kind, args);
  }

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */

  /**
   * Create a Boolean {@code true} constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkTrue()}.
   * It will be removed in a future release.
   *
   * @return The true constant.
   */
  @Deprecated
  public Term mkTrue()
  {
    return d_tm.mkTrue();
  }

  /**
   * Create a Boolean {@code false} constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFalse()}.
   * It will be removed in a future release.
   *
   * @return The false constant.
   */
  @Deprecated
  public Term mkFalse()
  {
    return d_tm.mkFalse();
  }

  /**
   * Create a Boolean constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkBoolean(boolean)}.
   * It will be removed in a future release.
   *
   * @param val The value of the constant.
   * @return The Boolean constant.
   */
  @Deprecated
  public Term mkBoolean(boolean val)
  {
    return d_tm.mkBoolean(val);
  }

  /**
   * Create a constant representing the number Pi.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkPi()}.
   * It will be removed in a future release.
   *
   * @return A constant representing Pi.
   */
  @Deprecated
  public Term mkPi()
  {
    return d_tm.mkPi();
  }

  /**
   * Create an integer constant from a string.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkInteger(String)}.
   * It will be removed in a future release.
   *
   * @param s The string representation of the constant, may represent an.
   *          integer (e.g., "123").
   * @return A constant of sort Integer assuming {@code s} represents an
   *         integer).
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkInteger(String s) throws CVC5ApiException
  {
    return d_tm.mkInteger(s);
  }

  /**
   * Create an integer constant from a C++ {@code int}.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkInteger(long)}.
   * It will be removed in a future release.
   *
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  @Deprecated
  public Term mkInteger(long val)
  {
    return d_tm.mkInteger(val);
  }

  /**
   * Create a real constant from a string.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkReal(String)}.
   * It will be removed in a future release.
   *
   * @param s The string representation of the constant, may represent an.
   *          integer (e.g., "123") or real constant (e.g., "12.34" or
   * "12/34").
   * @return A constant of sort Real.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkReal(String s) throws CVC5ApiException
  {
    return d_tm.mkReal(s);
  }

  /**
   * Create a real constant from an integer.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkReal(long)}.
   * It will be removed in a future release.
   *
   * @param val The value of the constant.
   * @return A constant of sort Integer.
   */
  @Deprecated
  public Term mkReal(long val)
  {
    return d_tm.mkReal(val);
  }

  /**
   * Create a real constant from a rational.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkReal(long, long)}.
   * It will be removed in a future release.
   *
   * @param num The value of the numerator.
   * @param den The value of the denominator.
   * @return A constant of sort Real.
   */
  @Deprecated
  public Term mkReal(long num, long den)
  {
    return d_tm.mkReal(num, den);
  }

  /**
   * Create a regular expression none ({@code re.none}) term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkRegexpNone()}.
   * It will be removed in a future release.
   *
   * @return The none term.
   */
  @Deprecated
  public Term mkRegexpNone()
  {
    return d_tm.mkRegexpNone();
  }

  /**
   * Create a regular expression all ({@code re.all}) term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkRegexpAll()}.
   * It will be removed in a future release.
   *
   * @return The all term.
   */
  @Deprecated
  public Term mkRegexpAll()
  {
    return d_tm.mkRegexpAll();
  }

  /**
   * Create a regular expression allchar ({@code re.allchar}) term.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkRegexpAllchar()}.
   * It will be removed in a future release.
   *
   * @return The allchar term.
   */
  @Deprecated
  public Term mkRegexpAllchar()
  {
    return d_tm.mkRegexpAllchar();
  }

  /**
   * Create a constant representing an empty set of the given sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkEmptySet(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the set elements.
   * @return The empty set constant.
   */
  @Deprecated
  public Term mkEmptySet(Sort sort)
  {
    return d_tm.mkEmptySet(sort);
  }

  /**
   * Create a constant representing an empty bag of the given sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkEmptyBag(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the bag elements.
   * @return The empty bag constant.
   */
  @Deprecated
  public Term mkEmptyBag(Sort sort)
  {
    return d_tm.mkEmptyBag(sort);
  }

  /**
   * Create a separation logic empty term.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkSepEmp()}.
   * It will be removed in a future release.
   *
   * @return The separation logic empty term.
   */
  @Deprecated
  public Term mkSepEmp()
  {
    return d_tm.mkSepEmp();
  }

  /**
   * Create a separation logic nil term.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkSepNil(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the nil term.
   * @return The separation logic nil term.
   */
  @Deprecated
  public Term mkSepNil(Sort sort)
  {
    return d_tm.mkSepNil(sort);
  }

  /**
   * Create a String constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkString(String)}.
   * It will be removed in a future release.
   *
   * @param s The string this constant represents.
   * @return The String constant.
   */
  @Deprecated
  public Term mkString(String s)
  {
    return d_tm.mkString(s);
  }

  /**
   * Create a String constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkString(String, boolean)}.
   * It will be removed in a future release.
   *
   * @param s The string this constant represents.
   * @param useEscSequences Determines whether escape sequences in {@code s}
   *                        should be converted to the corresponding unicode
   *                        character.
   * @return The String constant.
   */
  @Deprecated
  public Term mkString(String s, boolean useEscSequences)
  {
    // TODO: review unicode https://github.com/cvc5/cvc5-wishues/issues/150
    return d_tm.mkString(s, useEscSequences);
  }

  /**
   * Create a String constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkString(int[])}.
   * It will be removed in a future release.
   *
   * @param s A list of unsigned (unicode) values this constant represents
   *          as string.
   * @return The String constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkString(int[] s) throws CVC5ApiException
  {
    return d_tm.mkString(s);
  }

  /**
   * Create an empty sequence of the given element sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkEmptySequence(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The element sort of the sequence.
   * @return The empty sequence with given element sort.
   */
  @Deprecated
  public Term mkEmptySequence(Sort sort)
  {
    return d_tm.mkEmptySequence(sort);
  }

  /**
   * Create a universe set of the given sort.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkUniverseSet(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the set elements.
   * @return The universe set constant.
   */
  @Deprecated
  public Term mkUniverseSet(Sort sort)
  {
    return d_tm.mkUniverseSet(sort);
  }

  /**
   * Create a bit-vector constant of given size and value = 0.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkBitVector(int)}.
   * It will be removed in a future release.
   *
   * @param size The bit-width of the bit-vector sort.
   * @return The bit-vector constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkBitVector(int size) throws CVC5ApiException
  {
    return d_tm.mkBitVector(size);
  }

  /**
   * Create a bit-vector constant of given size and value.
   *
   * @api.note The given value must fit into a bit-vector of the given size.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkBitVector(int, long)}.
   * It will be removed in a future release.
   *
   * @param size The bit-width of the bit-vector sort.
   * @param val The value of the constant.
   * @return The bit-vector constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkBitVector(int size, long val) throws CVC5ApiException
  {
    return d_tm.mkBitVector(size, val);
  }

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * @api.note The given value must fit into a bit-vector of the given size.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkBitVector(int, String, int)}.
   * It will be removed in a future release.
   *
   * @param size The bit-width of the constant.
   * @param s The string representation of the constant.
   * @param base The base of the string representation (2, 10, or 16)
   * @return The bit-vector constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkBitVector(int size, String s, int base) throws CVC5ApiException
  {
    return d_tm.mkBitVector(size, s, base);
  }

  /**
   * Create a finite field constant in a given field and for a given value.
   *
   * @api.note The given value must fit into a the given finite field.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFiniteFieldElem(String, Sort, int)}.
   * It will be removed in a future release.
   *
   * @param val The value of the constant.
   * @param sort The sort of the finite field.
   * @param base The base of the string representation.
   * @return The finite field constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFiniteFieldElem(String val, Sort sort, int base) throws CVC5ApiException
  {
    return d_tm.mkFiniteFieldElem(val, sort, base);
  }

  /**
   * Create a constant array with the provided constant value stored at
   * every index
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkConstArray(Sort, Term)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the constant array (must be an array sort)
   * @param val The constant value to store (must match the sort's element
   *            sort).
   * @return The constant array term.
   */
  @Deprecated
  public Term mkConstArray(Sort sort, Term val)
  {
    return d_tm.mkConstArray(sort, val);
  }

  /**
   * Create a positive infinity floating-point constant (SMT-LIB: {@code +oo}).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPointPosInf(int, int)}.
   * It will be removed in a future release.
   *
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPointPosInf(int exp, int sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPointPosInf(exp, sig);
  }

  /**
   * Create a negative infinity floating-point constant (SMT-LIB: {@code -oo}).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPointNegInf(int, int)}.
   * It will be removed in a future release.
   *
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPointNegInf(int exp, int sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPointNegInf(exp, sig);
  }

  /**
   * Create a not-a-number floating-point constant (SMT-LIB: {@code NaN}).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPointNaN(int, int)}.
   * It will be removed in a future release.
   *
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPointNaN(int exp, int sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPointNaN(exp, sig);
  }

  /**
   * Create a positive zero floating-point constant (SMT-LIB: {@code +zero}).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPointPosZero(int, int)}.
   * It will be removed in a future release.
   *
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPointPosZero(int exp, int sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPointPosZero(exp, sig);
  }

  /**
   * Create a negative zero floating-point constant (SMT-LIB: {@code -zero}).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPointNegZero(int, int)}.
   * It will be removed in a future release.
   *
   * @param exp Number of bits in the exponent.
   * @param sig Number of bits in the significand.
   * @return The floating-point constant.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPointNegZero(int exp, int sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPointNegZero(exp, sig);
  }

  /**
   * Create a rounding mode constant.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkRoundingMode(RoundingMode)}.
   * It will be removed in a future release.
   *
   * @param rm The floating point rounding mode this constant represents.
   * @return The rounding mode.
   */
  @Deprecated
  public Term mkRoundingMode(RoundingMode rm)
  {
    return d_tm.mkRoundingMode(rm);
  }

  /**
   * Create a floating-point value from a bit-vector given in IEEE-754
   * format.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPoint(int, int, Term)}.
   * It will be removed in a future release.
   *
   * @param exp Size of the exponent.
   * @param sig Size of the significand.
   * @param val Value of the floating-point constant as a bit-vector term.
   * @return The floating-point value.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPoint(int exp, int sig, Term val) throws CVC5ApiException
  {
    return d_tm.mkFloatingPoint(exp, sig, val);
  }

  /**
   * Create a floating-point value from its three IEEE-754 bit-vector value
   * components (sign bit, exponent, significand).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkFloatingPoint(Term, Term, Term)}.
   * It will be removed in a future release.
   *
   * @param sign The sign bit.
   * @param exp  The bit-vector representing the exponent.
   * @param sig The bit-vector representing the significand.
   * @return The floating-point value.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkFloatingPoint(Term sign, Term exp, Term sig) throws CVC5ApiException
  {
    return d_tm.mkFloatingPoint(sign, exp, sig);
  }

  /**
   * Create a cardinality constraint for an uninterpreted sort.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkCardinalityConstraint(Sort, int)}.
   * It will be removed in a future release.
   *
   * @param sort The sort the cardinality constraint is for.
   * @param upperBound The upper bound on the cardinality of the sort.
   * @return The cardinality constraint.
   * @throws CVC5ApiException on error
   */
  @Deprecated
  public Term mkCardinalityConstraint(Sort sort, int upperBound) throws CVC5ApiException
  {
    return d_tm.mkCardinalityConstraint(sort, upperBound);
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
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkConst(Sort, String)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the constant.
   * @param symbol The name of the constant.
   * @return The first-order constant.
   */
  @Deprecated
  public Term mkConst(Sort sort, String symbol)
  {
    return d_tm.mkConst(sort, symbol);
  }

  /**
   * Create a free constant with a default symbol name.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkConst(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the constant.
   * @return The first-order constant.
   */
  @Deprecated
  public Term mkConst(Sort sort)
  {
    return d_tm.mkConst(sort);
  }

  /**
   * Create a bound variable to be used in a binder (i.e., a quantifier, a
   * lambda, or a witness binder).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkVar(Sort)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the variable.
   * @return The variable.
   */
  @Deprecated
  public Term mkVar(Sort sort)
  {
    return d_tm.mkVar(sort);
  }

  /**
   * Create a bound variable to be used in a binder (i.e., a quantifier, a
   * lambda, or a witness binder).
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkVar(Sort, String)}.
   * It will be removed in a future release.
   *
   * @param sort The sort of the variable.
   * @param symbol The name of the variable.
   * @return The variable.
   */
  @Deprecated
  public Term mkVar(Sort sort, String symbol)
  {
    return d_tm.mkVar(sort, symbol);
  }

  /* .................................................................... */
  /* Create datatype constructor declarations                             */
  /* .................................................................... */

  /**
   * Create a datatype constructor declaration.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeConstructorDecl(String)}.
   * It will be removed in a future release.
   *
   * @param name The name of the datatype constructor.
   * @return The DatatypeConstructorDecl.
   */
  @Deprecated
  public DatatypeConstructorDecl mkDatatypeConstructorDecl(String name)
  {
    return d_tm.mkDatatypeConstructorDecl(name);
  }

  /* .................................................................... */
  /* Create datatype declarations                                         */
  /* .................................................................... */

  /**
   * Create a datatype declaration.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeDecl(String)}.
   * It will be removed in a future release.
   *
   * @param name The name of the datatype.
   * @return The DatatypeDecl.
   */
  @Deprecated
  public DatatypeDecl mkDatatypeDecl(String name)
  {
    return d_tm.mkDatatypeDecl(name);
  }

  /**
   * Create a datatype declaration.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeDecl(String, boolean)}.
   * It will be removed in a future release.
   *
   * @param name The name of the datatype.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  @Deprecated
  public DatatypeDecl mkDatatypeDecl(String name, boolean isCoDatatype)
  {
    return d_tm.mkDatatypeDecl(name, isCoDatatype);
  }

  /**
   * Create a datatype declaration.
   *
   * Create sorts parameter with {@link TermManager#mkParamSort(String)}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeDecl(String, Sort[])}.
   * It will be removed in a future release.
   *
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @return The DatatypeDecl.
   */
  @Deprecated
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params)
  {
    return d_tm.mkDatatypeDecl(name, params);
  }

  /**
   * Create a datatype declaration.
   *
   * Create sorts parameter with {@link TermManager#mkParamSort(String)}.
   *
   * @deprecated
   * This function is deprecated and replaced by
   * {@link TermManager#mkDatatypeDecl(String, Sort[])}.
   * It will be removed in a future release.
   *
   * @param name The name of the datatype.
   * @param params A list of sort parameters.
   * @param isCoDatatype True if a codatatype is to be constructed.
   * @return The DatatypeDecl.
   */
  @Deprecated
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params, boolean isCoDatatype)
  {
    return d_tm.mkDatatypeDecl(name, params, isCoDatatype);
  }

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a term or formula based on rewriting.
   *
   * @api.note This function is experimental and may change in future versions.
   *
   * @param t The term to simplify.
   * @return The simplified term.
   */
  public Term simplify(Term t)
  {
    long termPointer = simplify(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long simplify(long pointer, long termPointer);

  /**
   * Simplify a term or formula based on rewriting and (optionally) applying
   * substitutions for solved variables.
   *
   * If applySubs is true, then for example, if `(= x 0)` was asserted to this
   * solver, this method may replace occurrences of `x` with `0`.
   *
   * @api.note This function is experimental and may change in future versions.
   *
   * @param t The term to simplify.
   * @param applySubs Whether to apply substitutions for solved variables.
   * @return The simplified term.
   */
  public Term simplify(Term t, boolean applySubs)
  {
    long termPointer = simplify(pointer, t.getPointer(), applySubs);
    return new Term(termPointer);
  }

  private native long simplify(long pointer, long termPointer, boolean applySubs);
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
   * @param fresh If true, then this method always returns a new Term.
   * Otherwise, this method will always return the same Term
   * for each call with the given sorts and symbol where fresh is false.
   * @return The function.
   */
  public Term declareFun(String symbol, Sort[] sorts, Sort sort, boolean fresh)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareFun(pointer, symbol, sortPointers, sort.getPointer(), fresh);
    return new Term(termPointer);
  }

  private native long declareFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer, boolean fresh);
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
   * @throws CVC5ApiException on error
   */
  public Sort declareSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = declareSort(pointer, symbol, arity);
    return new Sort(sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity);

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
   * @param fresh If true, then this method always returns a new Sort.
   * Otherwise, this method will always return the same Sort
   * for each call with the given arity and symbol where fresh is false.
   * @return The sort.
   * @throws CVC5ApiException on error
   */
  public Sort declareSort(String symbol, int arity, boolean fresh) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = declareSort(pointer, symbol, arity, fresh);
    return new Sort(sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity, boolean fresh);

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
   * Create parameter {@code fun} with {@link TermManager#mkConst(Sort)}.
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
   * Create parameter {@code fun} with {@link TermManager#mkConst(Sort)}.
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
   * {@link TermManager#mkConst(Sort)}.
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
   * {@link TermManager#mkConst(Sort)}.
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
   * @param flag The {@code get-info} flag.
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
   * @param option The name of the option.
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
   * Get the lemmas used to derive unsatisfiability.
   * SMT-LIB:
   * {@code
   * (get-unsat-core-lemmas)
   * }
   * Requires the SAT proof unsat core mode, so to enable option {@code unsat-core-mode=sat-proof}
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return A set of terms representing the lemmas used to derive
   * unsatisfiability.
   */
  public Term[] getUnsatCoreLemmas()
  {
    long[] retPointers = getUnsatCoreLemmas(pointer);
    return Utils.getTerms(retPointers);
  }

  private native long[] getUnsatCoreLemmas(long pointer);

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
   * Get a timeout core, which computes a subset of the given assumptions that
   * cause a timeout when added to the current assertions. Note it does not
   * require being proceeded by a call to checkSat.
   *
   * SMT-LIB:
   * {@code
   * (get-timeout-core)
   * }
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param assumptions The formulas to assume.
   * @return The result of the timeout core computation. This is a pair
   * containing a result and a list of formulas. If the result is unknown
   * and the reason is timeout, then the list of formulas correspond to a
   * subset of assumptions that cause a timeout when added to the current
   * assertions in the specified time {@code timeout-core-timeout}.
   * If the result is unsat, then the list of formulas plus the current
   * assertions correspond to an unsat core for the current assertions.
   * Otherwise, the result is sat, indicating that the given assumptions plus
   * the current assertions are satisfiable, and the list of formulas is empty.
   *
   * This method may make multiple checks for satisfiability internally, each
   * limited by the timeout value given by {@code timeout-core-timeout}.
   */
  public Pair<Result, Term[]> getTimeoutCoreAssuming(Term[] assumptions)
  {
    long[] pointers = Utils.getPointers(assumptions);
    Pair<Long, long[]> pair = getTimeoutCoreAssuming(pointer, pointers);
    Result result = new Result(pair.first);
    Term[] terms = Utils.getTerms(pair.second);
    Pair<Result, Term[]> ret = new Pair<>(result, terms);
    return ret;
  }

  private native Pair<Long, long[]> getTimeoutCoreAssuming(long pointer, long[] assumptionPointers);

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
   * @return A vector of proof nodes. This is equivalent to getProof
   * when c is FULL.
   */
  public Proof[] getProof()
  {
    return Utils.getProofs(getProof(pointer));
  }

  private native long[] getProof(long pointer);

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
   * @return A vector of proof nodes.
   */
  public Proof[] getProof(ProofComponent c)
  {
    return Utils.getProofs(getProof(pointer, c.getValue()));
  }

  private native long[] getProof(long pointer, int c);

  /**
   * Prints a proof into a string with a slected proof format mode.
   * Other aspects of printing are taken from the solver options.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param proof A proof.
   * @return The proof printed in the current format.
   */
  public String proofToString(Proof proof)
  {
    return proofToString(pointer, proof.getPointer());
  }

  private native String proofToString(long pointer, long proofs);

  /**
   * Prints a proof into a string with a slected proof format mode.
   * Other aspects of printing are taken from the solver options.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param proof A proof.
   * @param format The proof format used to print the proof. Must be
   * `PROOF_FORMAT_NONE` if the proof is from a component other than
   * `PROOF_COMPONENT_FULL`.
   * @return The proof printed in the current format.
   */
  public String proofToString(Proof proof, ProofFormat format)
  {
    return proofToString(pointer, proof.getPointer(), format.getValue());
  }

  private native String proofToString(long pointer, long proofs, int format);

  /**
   * Prints a proof into a string with a slected proof format mode.
   * Other aspects of printing are taken from the solver options.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param proof A proof.
   * @param format The proof format used to print the proof. Must be
   * `PROOF_FORMAT_NONE` if the proof is from a component other than
   * `PROOF_COMPONENT_FULL`.
   * @param assertionNames Mapping between assertions and names, if they were
   * given by the user.  This is used by the Alethe proof format.
   * @return The proof printed in the current format.
   */
  public String proofToString(Proof proof, ProofFormat format, Map assertionNames)
  {
    return proofToString(pointer, proof.getPointer(), format.getValue(), assertionNames);
  }

  private native String proofToString(long pointer, long proofs, int format, Map assertionNames);

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
   * @return The pool.
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
   * Add plugin to this solver. Its callbacks will be called throughout the
   * lifetime of this solver.
   *
   * @param p The plugin to add to this solver.
   */
  public void addPlugin(AbstractPlugin p)
  {
    addPlugin(pointer, p.getTermManager().getPointer(), p);
  }

  private native void addPlugin(long pointer, long termManagerPointer, AbstractPlugin p);

  /**
   * Pop a level from the assertion stack.
   *
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   *
   * @throws CVC5ApiException on error
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
   * @throws CVC5ApiException on error
   */
  public void pop(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    pop(pointer, nscopes);
  }

  private native void pop(long pointer, int nscopes);

  /**
   * Get an interpolant.
   *
   * <p>
   * Given that {@code A->B} is valid,
   * this function determines a term {@code I} 
   * over the shared variables of {@code A} and
   * {@code B},
   * such that {@code A->I} and {@code I->B}
   * are valid. {@code A} is the current set of
   * assertions and {@code B} is the conjecture, given as {@code conj}.
   * </p>
   *
   * SMT-LIB:
   * {@code
   * ( get-interpolant <symbol> <conj> )
   * }
   *
   * @api.note In SMT-LIB, {@code <symbol>} assigns a symbol to the interpolant.
   *
   * @api.note Requires option {@code produce-interpolants} to be set to a mode
   * different from {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @return The interpolant, if an interpolant exists, else the null term.
   */
  public Term getInterpolant(Term conj)
  {
    long interpolPtr = getInterpolant(pointer, conj.getPointer());
    return new Term(interpolPtr);
  }

  private native long getInterpolant(long pointer, long conjPointer);

  /**
   * Get an interpolant.
   *
   * <p>
   * Given that {@code A->B} is valid,
   * this function determines a term {@code I}, 
   * over the shared variables of {@code A} and
   * {@code B},
   * with respect to a given grammar, such
   * that {@code A->I} and {@code I->B} are valid, if such a term exits.
   * {@code A} is the current set of assertions and {@code B} is the
   * conjecture, given as {@code conj}.
   * </p>
   *
   * SMT-LIB:
   * {@code
   * ( get-interpolant <symbol> <conj> <g> )
   * }
   *
   * @api.note In SMT-LIB, {@code <symbol>} assigns a symbol to the interpolant.
   *
   * @api.note Requires option {@code produce-interpolants} to be set to a mode
   * different from {@code none}.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @param conj The conjecture term.
   * @param grammar The grammar for the interpolant {@code I}.
   * @return The interpolant, if an interpolant exists, else the null term.
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
   *
   * @param terms The model values to block.
   */
  public void blockModelValues(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    blockModelValues(pointer, pointers);
  }

  private native void blockModelValues(long pointer, long[] termPointers);

  /**
   * Get a string that contains information about all instantiations made by
   * the quantifiers module.
   *
   * @api.note This method is experimental and may change in future versions.
   *
   * @return The string representing the information about all instantiations.
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
   * @throws CVC5ApiException on error
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
   * @throws CVC5ApiException on error
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
   * @throws CVC5ApiException on error
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
   * @throws CVC5ApiException on error
   */
  public void setLogic(String logic) throws CVC5ApiException
  {
    setLogic(pointer, logic);
  }

  private native void setLogic(long pointer, String logic) throws CVC5ApiException;

  /**
   * Is logic set? Returns whether we called setLogic yet for this solver.
   *
   * @return whether we called setLogic yet for this solver.
   */
  public boolean isLogicSet()
  {
    return isLogicSet(pointer);
  }

  private native boolean isLogicSet(long pointer);

  /**
   * Get the logic set the solver.
   *
   * @api.note Asserts isLogicSet().
   *
   * @return The logic used by the solver.
   * @throws CVC5ApiException on error
   */
  public String getLogic() throws CVC5ApiException
  {
    return getLogic(pointer);
  }

  private native String getLogic(long pointer) throws CVC5ApiException;

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
   * Find a target term of interest using sygus enumeration, with no provided
   * grammar.
   *
   * The solver will infer which grammar to use in this call, which by default
   * will be the grammars specified by the function(s)-to-synthesize in the
   * current context.
   *
   * SyGuS v2:
   * {@code
   *     (find-synth :target)
   * }
   *
   * @param fst The identifier specifying what kind of term to find
   * @return The result of the find, which is the null term if this call failed.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Term findSynth(FindSynthTarget fst)
  {
    long termPointer = findSynth(pointer, fst.getValue());
    return new Term(termPointer);
  }
  private native long findSynth(long pointer, int fst);

  /**
   * Find a target term of interest using sygus enumeration with a provided
   * grammar.
   *
   * SyGuS v2:
   * {@code
   *     (find-synth :target G)
   * }
   *
   * @param fst The identifier specifying what kind of term to find
   * @param grammar The grammar for the term
   * @return The result of the find, which is the null term if this call failed.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Term findSynth(FindSynthTarget fst, Grammar grammar)
  {
    long termPointer = findSynth(pointer, fst.getValue(), grammar.getPointer());
    return new Term(termPointer);
  }
  private native long findSynth(long pointer, int fst, long grammarPointer);

  /**
   * Try to find a next target term of interest using sygus enumeration. Must
   * be called immediately after a successful call to find-synth or
   * find-synth-next.
   *
   * SyGuS v2:
   * {@code
   *     (find-synth-next)
   * }
   *
   * @return The result of the find, which is the null term if this call failed.
   *
   * @api.note This method is experimental and may change in future versions.
   */
  public Term findSynthNext()
  {
    long termPointer = findSynthNext(pointer);
    return new Term(termPointer);
  }

  private native long findSynthNext(long pointer);

  /**
   * Get a snapshot of the current state of the statistic values of this
   * solver. The returned object is completely decoupled from the solver and
   * will not change when the solver is used again.
   * @return A snapshot of the current state of the statistic values.
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
