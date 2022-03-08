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

import java.io.IOException;
import java.util.*;

public class Solver implements IPointer, AutoCloseable
{
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

  // store pointers for terms, sorts, etc
  List<AbstractPointer> abstractPointers = new ArrayList<>();

  @Override public void close()
  {
    // delete heap memory for terms, sorts, etc
    for (int i = abstractPointers.size() - 1; i >= 0; i--)
    {
      abstractPointers.get(i).deletePointer();
    }
    // delete the heap memory for this solver
    deletePointer();
  }

  void addAbstractPointer(AbstractPointer abstractPointer)
  {
    abstractPointers.add(abstractPointer);
  }

  static
  {
    Utils.loadLibraries();
  }

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
   * @return sort null
   */

  public Sort getNullSort()
  {
    long sortPointer = getNullSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getNullSort(long pointer);

  /**
   * @return sort Boolean
   */
  public Sort getBooleanSort()
  {
    long sortPointer = getBooleanSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getBooleanSort(long pointer);

  /**
   * @return sort Integer (in cvc5, Integer is a subtype of Real)
   */
  public Sort getIntegerSort()
  {
    long sortPointer = getIntegerSort(pointer);
    return new Sort(this, sortPointer);
  }

  public native long getIntegerSort(long pointer);
  /**
   * @return sort Real
   */
  public Sort getRealSort()
  {
    long sortPointer = getRealSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getRealSort(long pointer);
  /**
   * @return sort RegExp
   */
  public Sort getRegExpSort()
  {
    long sortPointer = getRegExpSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getRegExpSort(long pointer);
  /**
   * @return sort RoundingMode
   */
  public Sort getRoundingModeSort() throws CVC5ApiException
  {
    long sortPointer = getRoundingModeSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getRoundingModeSort(long pointer) throws CVC5ApiException;
  /**
   * @return sort String
   */
  public Sort getStringSort()
  {
    long sortPointer = getStringSort(pointer);
    return new Sort(this, sortPointer);
  }

  private native long getStringSort(long solverPointer);
  /**
   * Create an array sort.
   * @param indexSort the array index sort
   * @param elemSort the array element sort
   * @return the array sort
   */
  public Sort mkArraySort(Sort indexSort, Sort elemSort)
  {
    long sortPointer = mkArraySort(pointer, indexSort.getPointer(), elemSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkArraySort(long pointer, long indexSortPointer, long elementSortPointer);

  /**
   * Create a bit-vector sort.
   * @param size the bit-width of the bit-vector sort
   * @return the bit-vector sort
   */
  public Sort mkBitVectorSort(int size) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    long sortPointer = mkBitVectorSort(pointer, size);
    return new Sort(this, sortPointer);
  }

  private native long mkBitVectorSort(long pointer, int size);

  /**
   * Create a floating-point sort.
   * @param exp the bit-width of the exponent of the floating-point sort.
   * @param sig the bit-width of the significand of the floating-point sort.
   */
  public Sort mkFloatingPointSort(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long sortPointer = mkFloatingPointSort(pointer, exp, sig);
    return new Sort(this, sortPointer);
  }

  private native long mkFloatingPointSort(long solverPointer, int exp, int sig);

  /**
   * Create a datatype sort.
   * @param dtypedecl the datatype declaration from which the sort is
   *     created
   * @return the datatype sort
   */
  public Sort mkDatatypeSort(DatatypeDecl dtypedecl) throws CVC5ApiException
  {
    long pointer = mkDatatypeSort(this.pointer, dtypedecl.getPointer());
    return new Sort(this, pointer);
  }

  private native long mkDatatypeSort(long pointer, long datatypeDeclPointer)
      throws CVC5ApiException;

  /**
   * Create a vector of datatype sorts. The names of the datatype
   * declarations must be distinct.
   *
   * @param dtypedecls the datatype declarations from which the sort is
   *     created
   * @return the datatype sorts
   */
  public Sort[] mkDatatypeSorts(List<DatatypeDecl> dtypedecls) throws CVC5ApiException
  {
    return mkDatatypeSorts(dtypedecls.toArray(new DatatypeDecl[0]));
  }

  /**
   * Create a vector of datatype sorts. The names of the datatype
   * declarations must be distinct.
   *
   * @param dtypedecls the datatype declarations from which the sort is
   *     created
   * @return the datatype sorts
   */
  public Sort[] mkDatatypeSorts(DatatypeDecl[] dtypedecls) throws CVC5ApiException
  {
    long[] declPointers = Utils.getPointers(dtypedecls);
    long[] sortPointers = mkDatatypeSorts(pointer, declPointers);
    Sort[] sorts = Utils.getSorts(this, sortPointers);
    return sorts;
  }

  private native long[] mkDatatypeSorts(long pointer, long[] declPointers) throws CVC5ApiException;

  /**
   * Create a vector of datatype sorts using unresolved sorts. The names of
   * the datatype declarations in dtypedecls must be distinct.
   *
   * This method is called when the DatatypeDecl objects dtypedecls have
   * been built using "unresolved" sorts.
   *
   * We associate each sort in unresolvedSorts with exacly one datatype from
   * dtypedecls. In particular, it must have the same name as exactly one
   * datatype declaration in dtypedecls.
   *
   * When constructing datatypes, unresolved sorts are replaced by the
   * datatype sort constructed for the datatype declaration it is associated
   * with.
   *
   * @apiNote Create unresolved sorts with Solver::mkUnresolvedSort().
   *
   * @param dtypedecls the datatype declarations from which the sort is
   *     created
   * @param unresolvedSorts the set of unresolved sorts
   * @return the datatype sorts
   */
  public List<Sort> mkDatatypeSorts(List<DatatypeDecl> dtypedecls, Set<Sort> unresolvedSorts)
      throws CVC5ApiException
  {
    Sort[] array = mkDatatypeSorts(
        dtypedecls.toArray(new DatatypeDecl[0]), unresolvedSorts.toArray(new Sort[0]));
    return Arrays.asList(array);
  }

  /**
   * Create a vector of datatype sorts using unresolved sorts. The names of
   * the datatype declarations in dtypedecls must be distinct.
   *
   * This method is called when the DatatypeDecl objects dtypedecls have
   * been built using "unresolved" sorts.
   *
   * We associate each sort in unresolvedSorts with exacly one datatype from
   * dtypedecls. In particular, it must have the same name as exactly one
   * datatype declaration in dtypedecls.
   *
   * When constructing datatypes, unresolved sorts are replaced by the
   * datatype sort constructed for the datatype declaration it is associated
   * with.
   *
   * @param dtypedecls the datatype declarations from which the sort is
   *     created
   * @param unresolvedSorts the list of unresolved sorts
   * @return the datatype sorts
   */
  public Sort[] mkDatatypeSorts(DatatypeDecl[] dtypedecls, Sort[] unresolvedSorts)
      throws CVC5ApiException
  {
    long[] declPointers = Utils.getPointers(dtypedecls);
    long[] unresolvedPointers = Utils.getPointers(unresolvedSorts);
    long[] sortPointers = mkDatatypeSorts(pointer, declPointers, unresolvedPointers);
    Sort[] sorts = Utils.getSorts(this, sortPointers);
    return sorts;
  }

  private native long[] mkDatatypeSorts(
      long pointer, long[] declPointers, long[] unresolvedPointers) throws CVC5ApiException;

  /**
   * Create function sort.
   * @param domain the sort of the fuction argument
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  public Sort mkFunctionSort(Sort domain, Sort codomain)
  {
    long sortPointer = mkFunctionSort(pointer, domain.getPointer(), codomain.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkFunctionSort(long pointer, long domainPointer, long codomainPointer);

  /**
   * Create function sort.
   * @param sorts the sort of the function arguments
   * @param codomain the sort of the function return value
   * @return the function sort
   */
  public Sort mkFunctionSort(Sort[] sorts, Sort codomain)
  {
    long sortPointer = mkFunctionSort(pointer, Utils.getPointers(sorts), codomain.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkFunctionSort(long pointer, long[] sortPointers, long codomainPointer);

  /**
   * Create a sort parameter.
   * @param symbol the name of the sort
   * @return the sort parameter
   */
  public Sort mkParamSort(String symbol)
  {
    long sortPointer = mkParamSort(pointer, symbol);
    return new Sort(this, sortPointer);
  }

  private native long mkParamSort(long pointer, String symbol);

  /**
   * Create a predicate sort.
   * @param sorts the list of sorts of the predicate
   * @return the predicate sort
   */
  public Sort mkPredicateSort(Sort[] sorts)
  {
    long sortPointer = mkPredicateSort(pointer, Utils.getPointers(sorts));
    return new Sort(this, sortPointer);
  }

  private native long mkPredicateSort(long pointer, long[] sortPointers);

  /**
   * Create a record sort
   * @param fields the list of fields of the record
   * @return the record sort
   */
  public Sort mkRecordSort(Pair<String, Sort>[] fields)
  {
    long sortPointer = mkRecordSort(pointer, Utils.getPairs(fields));
    return new Sort(this, sortPointer);
  }

  private native long mkRecordSort(long pointer, Pair<String, Long>[] fields);

  /**
   * Create a set sort.
   * @param elemSort the sort of the set elements
   * @return the set sort
   */
  public Sort mkSetSort(Sort elemSort)
  {
    long sortPointer = mkSetSort(pointer, elemSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkSetSort(long pointer, long elemSortPointer);
  /**
   * Create a bag sort.
   * @param elemSort the sort of the bag elements
   * @return the bag sort
   */
  public Sort mkBagSort(Sort elemSort)
  {
    long sortPointer = mkBagSort(pointer, elemSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkBagSort(long pointer, long elemSortPointer);

  /**
   * Create a sequence sort.
   * @param elemSort the sort of the sequence elements
   * @return the sequence sort
   */
  public Sort mkSequenceSort(Sort elemSort)
  {
    long sortPointer = mkSequenceSort(pointer, elemSort.getPointer());
    return new Sort(this, sortPointer);
  }

  private native long mkSequenceSort(long pointer, long elemSortPointer);

  /**
   * Create an uninterpreted sort.
   * @param symbol the name of the sort
   * @return the uninterpreted sort
   */
  public Sort mkUninterpretedSort(String symbol)
  {
    long sortPointer = mkUninterpretedSort(pointer, symbol);
    return new Sort(this, sortPointer);
  }

  private native long mkUninterpretedSort(long pointer, String symbol);

  /**
   * Create an unresolved sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive datatypes.
   *
   * @param symbol the symbol of the sort
   * @param arity the number of sort parameters of the sort
   * @return the unresolved sort
   */
  public Sort mkUnresolvedSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = mkUnresolvedSort(pointer, symbol, arity);
    return new Sort(this, sortPointer);
  }

  private native long mkUnresolvedSort(long pointer, String symbol, int arity);

  /**
   * Create an unresolved sort.
   *
   * This is for creating yet unresolved sort placeholders for mutually
   * recursive datatypes without sort parameters.
   *
   * @param symbol the symbol of the sort
   * @return the unresolved sort
   */
  public Sort mkUnresolvedSort(String symbol) throws CVC5ApiException
  {
    return mkUnresolvedSort(symbol, 0);
  }

  /**
   * Create a sort constructor sort.
   * @param symbol the symbol of the sort
   * @param arity the arity of the sort
   * @return the sort constructor sort
   */
  public Sort mkSortConstructorSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = mkSortConstructorSort(pointer, symbol, arity);
    return new Sort(this, sortPointer);
  }

  private native long mkSortConstructorSort(long pointer, String symbol, int arity);

  /**
   * Create a tuple sort.
   * @param sorts of the elements of the tuple
   * @return the tuple sort
   */
  public Sort mkTupleSort(Sort[] sorts)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long sortPointer = mkTupleSort(pointer, sortPointers);
    return new Sort(this, sortPointer);
  }

  private native long mkTupleSort(long pointer, long[] sortPointers);

  /* .................................................................... */
  /* Create Terms                                                         */
  /* .................................................................... */

  /**
   * Create 0-ary term of given kind.
   * @param kind the kind of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind)
  {
    long termPointer = mkTerm(pointer, kind.getValue());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, int kindValue);

  /**
   * Create a unary term of given kind.
   * @param kind the kind of the term
   * @param child the child of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term child)
  {
    long termPointer = mkTerm(pointer, kind.getValue(), child.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, int kindValue, long childPointer);

  /**
   * Create binary term of given kind.
   * @param kind the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term child1, Term child2)
  {
    long termPointer = mkTerm(pointer, kind.getValue(), child1.getPointer(), child2.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, int kindValue, long child1Pointer, long child2Pointer);

  /**
   * Create ternary term of given kind.
   * @param kind the kind of the term
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @param child3 the third child of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term child1, Term child2, Term child3)
  {
    long termPointer = mkTerm(
        pointer, kind.getValue(), child1.getPointer(), child2.getPointer(), child3.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(
      long pointer, int kindValue, long child1Pointer, long child2Pointer, long child3Pointer);
  /**
   * Create n-ary term of given kind.
   * @param kind the kind of the term
   * @param children the children of the term
   * @return the Term
   */
  public Term mkTerm(Kind kind, Term[] children)
  {
    long[] childPointers = Utils.getPointers(children);
    long termPointer = mkTerm(pointer, kind.getValue(), childPointers);
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, int kindValue, long[] childrenPointers);

  /**
   * Create nullary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @return the Term
   */
  public Term mkTerm(Op op)
  {
    long termPointer = mkTerm(pointer, op.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, long opPointer);
  /**
   * Create unary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param child the child of the term
   * @return the Term
   */
  public Term mkTerm(Op op, Term child)
  {
    long termPointer = mkTerm(pointer, op.getPointer(), child.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, long opPointer, long childPointer);

  /**
   * Create binary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @return the Term
   */
  public Term mkTerm(Op op, Term child1, Term child2)
  {
    long termPointer = mkTerm(pointer, op.getPointer(), child1.getPointer(), child2.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, long opPointer, long child1Pointer, long child2Pointer);
  /**
   * Create ternary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param child1 the first child of the term
   * @param child2 the second child of the term
   * @param child3 the third child of the term
   * @return the Term
   */
  public Term mkTerm(Op op, Term child1, Term child2, Term child3)
  {
    long termPointer =
        mkTerm(op.getPointer(), child1.getPointer(), child2.getPointer(), child3.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkTerm(
      long pointer, long opPointer, long child1Pointer, long child2Pointer, long child3Pointer);

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param children the children of the term
   * @return the Term
   */
  public Term mkTerm(Op op, List<Term> children)
  {
    return mkTerm(op, children.toArray(new Term[0]));
  }

  /**
   * Create n-ary term of given kind from a given operator.
   * Create operators with mkOp().
   * @param op the operator
   * @param children the children of the term
   * @return the Term
   */
  public Term mkTerm(Op op, Term[] children)
  {
    long[] childPointers = Utils.getPointers(children);
    long termPointer = mkTerm(pointer, op.getPointer(), childPointers);
    return new Term(this, termPointer);
  }

  private native long mkTerm(long pointer, long opPointer, long[] childrenPointers);

  /**
   * Create a tuple term. Terms are automatically converted if sorts are
   * compatible.
   * @param sorts The sorts of the elements in the tuple
   * @param terms The elements in the tuple
   * @return the tuple Term
   */
  public Term mkTuple(Sort[] sorts, Term[] terms)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long[] termPointers = Utils.getPointers(terms);
    long termPointer = mkTuple(pointer, sortPointers, termPointers);
    return new Term(this, termPointer);
  }

  private native long mkTuple(long pointer, long[] sortPointers, long[] termPointers);

  /* .................................................................... */
  /* Create Operators                                                     */
  /* .................................................................... */

  /**
   * Create an operator for a builtin Kind
   * The Kind may not be the Kind for an indexed operator
   *   (e.g. BITVECTOR_EXTRACT).
   * @apiNote In this case, the Op simply wraps the Kind. The Kind can be used
   *          in mkTerm directly without creating an op first.
   * @param kind the kind to wrap
   */
  public Op mkOp(Kind kind)
  {
    long opPointer = mkOp(pointer, kind.getValue());
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kindValue);
  /**
   * Create operator of kind:
   *   - RECORD_UPDATE
   *   - DIVISIBLE (to support arbitrary precision integers)
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg the string argument to this operator
   */
  public Op mkOp(Kind kind, String arg)
  {
    long opPointer = mkOp(pointer, kind.getValue(), arg);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kindValue, String arg);

  /**
   * Create operator of kind:
   *   - DIVISIBLE
   *   - BITVECTOR_REPEAT
   *   - BITVECTOR_ZERO_EXTEND
   *   - BITVECTOR_SIGN_EXTEND
   *   - BITVECTOR_ROTATE_LEFT
   *   - BITVECTOR_ROTATE_RIGHT
   *   - INT_TO_BITVECTOR
   *   - FLOATINGPOINT_TO_UBV
   *   - FLOATINGPOINT_TO_UBV_TOTAL
   *   - FLOATINGPOINT_TO_SBV
   *   - FLOATINGPOINT_TO_SBV_TOTAL
   *   - TUPLE_UPDATE
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg the unsigned int argument to this operator
   */
  public Op mkOp(Kind kind, int arg) throws CVC5ApiException
  {
    Utils.validateUnsigned(arg, "arg");
    long opPointer = mkOp(pointer, kind.getValue(), arg);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kindValue, int arg);

  /**
   * Create operator of Kind:
   *   - BITVECTOR_EXTRACT
   *   - FLOATINGPOINT_TO_FP_IEEE_BITVECTOR
   *   - FLOATINGPOINT_TO_FP_FLOATINGPOINT
   *   - FLOATINGPOINT_TO_FP_REAL
   *   - FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR
   *   - FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR
   *   - FLOATINGPOINT_TO_FP_GENERIC
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param arg1 the first unsigned int argument to this operator
   * @param arg2 the second unsigned int argument to this operator
   */
  public Op mkOp(Kind kind, int arg1, int arg2) throws CVC5ApiException
  {
    Utils.validateUnsigned(arg1, "arg1");
    Utils.validateUnsigned(arg2, "arg2");
    long opPointer = mkOp(pointer, kind.getValue(), arg1, arg2);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kindValue, int arg1, int arg2);

  /**
   * Create operator of Kind:
   *   - TUPLE_PROJECT
   * See enum Kind for a description of the parameters.
   * @param kind the kind of the operator
   * @param args the arguments (indices) of the operator
   */
  public Op mkOp(Kind kind, int[] args) throws CVC5ApiException
  {
    Utils.validateUnsigned(args, "args");
    long opPointer = mkOp(pointer, kind.getValue(), args);
    return new Op(this, opPointer);
  }

  private native long mkOp(long pointer, int kindValue, int[] args);

  /* .................................................................... */
  /* Create Constants                                                     */
  /* .................................................................... */

  /**
   * Create a Boolean true constant.
   * @return the true constant
   */
  public Term mkTrue()
  {
    long termPointer = mkTrue(pointer);
    return new Term(this, termPointer);
  }

  private native long mkTrue(long pointer);
  /**
   * Create a Boolean false constant.
   * @return the false constant
   */
  public Term mkFalse()
  {
    long termPointer = mkFalse(pointer);
    return new Term(this, termPointer);
  }

  private native long mkFalse(long pointer);
  /**
   * Create a Boolean constant.
   * @return the Boolean constant
   * @param val the value of the constant
   */
  public Term mkBoolean(boolean val)
  {
    long termPointer = mkBoolean(pointer, val);
    return new Term(this, termPointer);
  }

  private native long mkBoolean(long pointer, boolean val);
  /**
   * Create a constant representing the number Pi.
   * @return a constant representing Pi
   */
  public Term mkPi()
  {
    long termPointer = mkPi(pointer);
    return new Term(this, termPointer);
  }

  private native long mkPi(long pointer);
  /**
   * Create an integer constant from a string.
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123").
   * @return a constant of sort Integer assuming 's' represents an integer)
   */
  public Term mkInteger(String s) throws CVC5ApiException
  {
    long termPointer = mkInteger(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkInteger(long pointer, String s) throws CVC5ApiException;

  /**
   * Create an integer constant from a c++ int.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  public Term mkInteger(long val)
  {
    long termPointer = mkInteger(pointer, val);
    return new Term(this, termPointer);
  }

  private native long mkInteger(long pointer, long val);
  /**
   * Create a real constant from a string.
   * @param s the string representation of the constant, may represent an
   *          integer (e.g., "123") or real constant (e.g., "12.34" or
   * "12/34").
   * @return a constant of sort Real
   */
  public Term mkReal(String s) throws CVC5ApiException
  {
    long termPointer = mkReal(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkReal(long pointer, String s) throws CVC5ApiException;
  /**
   * Create a real constant from an integer.
   * @param val the value of the constant
   * @return a constant of sort Integer
   */
  public Term mkReal(long val)
  {
    long termPointer = mkRealValue(pointer, val);
    return new Term(this, termPointer);
  }

  private native long mkRealValue(long pointer, long val);
  /**
   * Create a real constant from a rational.
   * @param num the value of the numerator
   * @param den the value of the denominator
   * @return a constant of sort Real
   */
  public Term mkReal(long num, long den)
  {
    long termPointer = mkReal(pointer, num, den);
    return new Term(this, termPointer);
  }

  private native long mkReal(long pointer, long num, long den);

  /**
   * Create a regular expression none (re.none) term.
   * @return the none term
   */
  public Term mkRegexpNone()
  {
    long termPointer = mkRegexpNone(pointer);
    return new Term(this, termPointer);
  }

  private native long mkRegexpNone(long pointer);

  /**
   * Create a regular expression all (re.all) term.
   * @return the all term
   */
  public Term mkRegexpAll()
  {
    long termPointer = mkRegexpAll(pointer);
    return new Term(this, termPointer);
  }

  private native long mkRegexpAll(long pointer);

  /**
   * Create a regular expression allchar (re.allchar) term.
   * @return the allchar term
   */
  public Term mkRegexpAllchar()
  {
    long termPointer = mkRegexpAllchar(pointer);
    return new Term(this, termPointer);
  }

  private native long mkRegexpAllchar(long pointer);

  /**
   * Create a constant representing an empty set of the given sort.
   * @param sort the sort of the set elements.
   * @return the empty set constant
   */
  public Term mkEmptySet(Sort sort)
  {
    long termPointer = mkEmptySet(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkEmptySet(long pointer, long sortPointer);
  /**
   * Create a constant representing an empty bag of the given sort.
   * @param sort the sort of the bag elements.
   * @return the empty bag constant
   */
  public Term mkEmptyBag(Sort sort)
  {
    long termPointer = mkEmptyBag(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkEmptyBag(long pointer, long sortPointer);

  /**
   * Create a separation logic empty term.
   * @return the separation logic empty term
   */
  public Term mkSepEmp()
  {
    long termPointer = mkSepEmp(pointer);
    return new Term(this, termPointer);
  }

  private native long mkSepEmp(long pointer);

  /**
   * Create a separation logic nil term.
   * @param sort the sort of the nil term
   * @return the separation logic nil term
   */
  public Term mkSepNil(Sort sort)
  {
    long termPointer = mkSepNil(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkSepNil(long pointer, long sortPointer);

  /**
   * Create a String constant.
   * @param s the string this constant represents
   * @return the String constant
   */
  public Term mkString(String s)
  {
    return mkString(s, false);
  }

  /**
   * Create a String constant.
   * @param s the string this constant represents
   * @param useEscSequences determines whether escape sequences in `s`
   * should be converted to the corresponding unicode character
   * @return the String constant
   */
  public Term mkString(String s, boolean useEscSequences)
  {
    // TODO: review unicode
    long termPointer = mkString(pointer, s, useEscSequences);
    return new Term(this, termPointer);
  }

  private native long mkString(long pointer, String s, boolean useEscSequences);

  /**
   * Create a String constant.
   * @param s a list of unsigned (unicode) values this constant represents
   *     as
   * string
   * @return the String constant
   */
  public Term mkString(int[] s) throws CVC5ApiException
  {
    Utils.validateUnsigned(s, "s");
    long termPointer = mkString(pointer, s);
    return new Term(this, termPointer);
  }

  private native long mkString(long pointer, int[] s);

  /**
   * Create an empty sequence of the given element sort.
   * @param sort The element sort of the sequence.
   * @return the empty sequence with given element sort.
   */
  public Term mkEmptySequence(Sort sort)
  {
    long termPointer = mkEmptySequence(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkEmptySequence(long pointer, long sortPointer);

  /**
   * Create a universe set of the given sort.
   * @param sort the sort of the set elements
   * @return the universe set constant
   */
  public Term mkUniverseSet(Sort sort)
  {
    long termPointer = mkUniverseSet(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkUniverseSet(long pointer, long sortPointer);

  /**
   * Create a bit-vector constant of given size and value = 0.
   * @param size the bit-width of the bit-vector sort
   * @return the bit-vector constant
   */
  public Term mkBitVector(int size) throws CVC5ApiException
  {
    return mkBitVector(size, 0);
  }

  /**
   * Create a bit-vector constant of given size and value.
   *
   * @apiNote The given value must fit into a bit-vector of the given size.
   *
   * @param size the bit-width of the bit-vector sort
   * @param val the value of the constant
   * @return the bit-vector constant
   */
  public Term mkBitVector(int size, long val) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    Utils.validateUnsigned(val, "val");
    long termPointer = mkBitVector(pointer, size, val);
    return new Term(this, termPointer);
  }

  private native long mkBitVector(long pointer, int size, long val);

  /**
   * Create a bit-vector constant of a given bit-width from a given string of
   * base 2, 10 or 16.
   *
   * @apiNote The given value must fit into a bit-vector of the given size.
   *
   * @param size the bit-width of the constant
   * @param s the string representation of the constant
   * @param base the base of the string representation (2, 10, or 16)
   * @return the bit-vector constant
   */
  public Term mkBitVector(int size, String s, int base) throws CVC5ApiException
  {
    Utils.validateUnsigned(size, "size");
    Utils.validateUnsigned(base, "base");
    long termPointer = mkBitVector(pointer, size, s, base);
    return new Term(this, termPointer);
  }

  private native long mkBitVector(long pointer, int size, String s, int base);

  /**
   * Create a constant array with the provided constant value stored at
   * every index
   * @param sort the sort of the constant array (must be an array sort)
   * @param val the constant value to store (must match the sort's element
   *     sort)
   * @return the constant array term
   */
  public Term mkConstArray(Sort sort, Term val)
  {
    long termPointer = mkConstArray(pointer, sort.getPointer(), val.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkConstArray(long pointer, long sortPointer, long valPointer);
  /**
   * Create a positive infinity floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  public Term mkFloatingPointPosInf(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointPosInf(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkFloatingPointPosInf(long pointer, int exp, int sig);
  /**
   * Create a negative infinity floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  public Term mkFloatingPointNegInf(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointNegInf(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkFloatingPointNegInf(long pointer, int exp, int sig);
  /**
   * Create a not-a-number (NaN) floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  public Term mkFloatingPointNaN(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointNaN(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkFloatingPointNaN(long pointer, int exp, int sig);

  /**
   * Create a positive zero (+0.0) floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  public Term mkFloatingPointPosZero(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointPosZero(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkFloatingPointPosZero(long pointer, int exp, int sig);

  /**
   * Create a negative zero (-0.0) floating-point constant.
   * @param exp Number of bits in the exponent
   * @param sig Number of bits in the significand
   * @return the floating-point constant
   */
  public Term mkFloatingPointNegZero(int exp, int sig) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPointNegZero(pointer, exp, sig);
    return new Term(this, termPointer);
  }

  private native long mkFloatingPointNegZero(long pointer, int exp, int sig);

  /**
   * Create a roundingmode constant.
   * @param rm the floating point rounding mode this constant represents
   */
  public Term mkRoundingMode(RoundingMode rm)
  {
    long termPointer = mkRoundingMode(pointer, rm.getValue());
    return new Term(this, termPointer);
  }

  private native long mkRoundingMode(long pointer, int rm);

  /**
   * Create a floating-point constant.
   * @param exp Size of the exponent
   * @param sig Size of the significand
   * @param val Value of the floating-point constant as a bit-vector term
   */
  public Term mkFloatingPoint(int exp, int sig, Term val) throws CVC5ApiException
  {
    Utils.validateUnsigned(exp, "exp");
    Utils.validateUnsigned(sig, "sig");
    long termPointer = mkFloatingPoint(pointer, exp, sig, val.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkFloatingPoint(long pointer, int exp, int sig, long valPointer);

  /**
   * Create a cardinality constraint for an uninterpreted sort.
   * @param sort the sort the cardinality constraint is for
   * @param upperBound the upper bound on the cardinality of the sort
   * @return the cardinality constraint
   */
  public Term mkCardinalityConstraint(Sort sort, int upperBound) throws CVC5ApiException
  {
    Utils.validateUnsigned(upperBound, "upperBound");
    long termPointer = mkCardinalityConstraint(pointer, sort.getPointer(), upperBound);
    return new Term(this, termPointer);
  }

  private native long mkCardinalityConstraint(long pointer, long sortPointer, int upperBound);

  /* .................................................................... */
  /* Create Variables                                                     */
  /* .................................................................... */

  /**
   * Create (first-order) constant (0-arity function symbol).
   * SMT-LIB:
   * {@code
   *   ( declare-const <symbol> <sort> )
   *   ( declare-fun <symbol> ( ) <sort> )
   * }
   *
   * @param sort the sort of the constant
   * @param symbol the name of the constant
   * @return the first-order constant
   */
  public Term mkConst(Sort sort, String symbol)
  {
    long termPointer = mkConst(pointer, sort.getPointer(), symbol);
    return new Term(this, termPointer);
  }

  private native long mkConst(long pointer, long sortPointer, String symbol);

  /**
   * Create (first-order) constant (0-arity function symbol), with a default
   * symbol name.
   *
   * @param sort the sort of the constant
   * @return the first-order constant
   */
  public Term mkConst(Sort sort)
  {
    long termPointer = mkConst(pointer, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long mkConst(long pointer, long sortPointer);

  /**
   * Create a bound variable to be used in a binder (i.e. a quantifier, a
   * lambda, or a witness binder).
   * @param sort the sort of the variable
   * @return the variable
   */
  public Term mkVar(Sort sort)
  {
    return mkVar(sort, "");
  }

  /**
   * Create a bound variable to be used in a binder (i.e. a quantifier, a
   * lambda, or a witness binder).
   * @param sort the sort of the variable
   * @param symbol the name of the variable
   * @return the variable
   */
  public Term mkVar(Sort sort, String symbol)
  {
    long termPointer = mkVar(pointer, sort.getPointer(), symbol);
    return new Term(this, termPointer);
  }

  private native long mkVar(long pointer, long sortPointer, String symbol);

  /* .................................................................... */
  /* Create datatype constructor declarations                             */
  /* .................................................................... */

  public DatatypeConstructorDecl mkDatatypeConstructorDecl(String name)
  {
    long declPointer = mkDatatypeConstructorDecl(pointer, name);
    return new DatatypeConstructorDecl(this, declPointer);
  }

  private native long mkDatatypeConstructorDecl(long pointer, String name);

  /* .................................................................... */
  /* Create datatype declarations                                         */
  /* .................................................................... */

  /**
   * Create a datatype declaration.
   * @param name the name of the datatype
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name)
  {
    return mkDatatypeDecl(name, false);
  }

  /**
   * Create a datatype declaration.
   * @param name the name of the datatype
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, boolean isCoDatatype)
  {
    long declPointer = mkDatatypeDecl(pointer, name, isCoDatatype);
    return new DatatypeDecl(this, declPointer);
  }

  private native long mkDatatypeDecl(long pointer, String name, boolean isCoDatatype);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param param the sort parameter
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort param)
  {
    return mkDatatypeDecl(name, param, false);
  }

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param param the sort parameter
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort param, boolean isCoDatatype)
  {
    long declPointer = mkDatatypeDecl(pointer, name, param.getPointer(), isCoDatatype);
    return new DatatypeDecl(this, declPointer);
  }

  private native long mkDatatypeDecl(
      long pointer, String name, long paramPointer, boolean isCoDatatype);

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, List<Sort> params)
  {
    return mkDatatypeDecl(name, params.toArray(new Sort[0]));
  }

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params)
  {
    return mkDatatypeDecl(name, params, false);
  }

  /**
   * Create a datatype declaration.
   * Create sorts parameter with Solver::mkParamSort().
   * @param name the name of the datatype
   * @param params a list of sort parameters
   * @param isCoDatatype true if a codatatype is to be constructed
   * @return the DatatypeDecl
   */
  public DatatypeDecl mkDatatypeDecl(String name, Sort[] params, boolean isCoDatatype)
  {
    long[] paramPointers = Utils.getPointers(params);
    long declPointer = mkDatatypeDecl(pointer, name, paramPointers, isCoDatatype);
    return new DatatypeDecl(this, declPointer);
  }

  private native long mkDatatypeDecl(
      long pointer, String name, long[] paramPointers, boolean isCoDatatype);

  /* .................................................................... */
  /* Formula Handling                                                     */
  /* .................................................................... */

  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   * @param t the formula to simplify
   * @return the simplified formula
   */
  public Term simplify(Term t)
  {
    long termPointer = simplify(pointer, t.getPointer());
    return new Term(this, termPointer);
  }

  private native long simplify(long pointer, long termPointer);

  /**
   * Assert a formula.
   * SMT-LIB:
   * {@code
   *   ( assert <term> )
   * }
   * @param term the formula to assert
   */
  public void assertFormula(Term term)
  {
    assertFormula(pointer, term.getPointer());
  }

  private native void assertFormula(long pointer, long termPointer);

  /**
   * Check satisfiability.
   * SMT-LIB:
   * {@code
   *   ( check-sat )
   * }
   * @return the result of the satisfiability check.
   */
  public Result checkSat()
  {
    long resultPointer = checkSat(pointer);
    return new Result(this, resultPointer);
  }

  private native long checkSat(long pointer);
  /**
   * Check satisfiability assuming the given formula.
   * SMT-LIB:
   * {@code
   *   ( check-sat-assuming ( <prop_literal> ) )
   * }
   * @param assumption the formula to assume
   * @return the result of the satisfiability check.
   */
  public Result checkSatAssuming(Term assumption)
  {
    long resultPointer = checkSatAssuming(pointer, assumption.getPointer());
    return new Result(this, resultPointer);
  }

  private native long checkSatAssuming(long pointer, long assumptionPointer);

  /**
   * Check satisfiability assuming the given formulas.
   * SMT-LIB:
   * {@code
   *   ( check-sat-assuming ( <prop_literal>+ ) )
   * }
   * @param assumptions the formulas to assume
   * @return the result of the satisfiability check.
   */
  public Result checkSatAssuming(Term[] assumptions)
  {
    long[] pointers = Utils.getPointers(assumptions);
    long resultPointer = checkSatAssuming(pointer, pointers);
    return new Result(this, resultPointer);
  }

  private native long checkSatAssuming(long pointer, long[] assumptionPointers);

  /**
   * Check entailment of the given formula w.r.t. the current set of assertions.
   * @param term the formula to check entailment for
   * @return the result of the entailment check.
   */
  public Result checkEntailed(Term term)
  {
    long resultPointer = checkEntailed(pointer, term.getPointer());
    return new Result(this, resultPointer);
  }

  private native long checkEntailed(long pointer, long termPointer);

  /**
   * Check entailment of the given set of given formulas w.r.t. the current
   * set of assertions.
   * @param terms the terms to check entailment for
   * @return the result of the entailmentcheck.
   */
  public Result checkEntailed(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    long resultPointer = checkEntailed(pointer, pointers);
    return new Result(this, resultPointer);
  }

  private native long checkEntailed(long pointer, long[] termPointers);

  /**
   * Create datatype sort.
   * SMT-LIB:
   * {@code
   *   ( declare-datatype <symbol> <datatype_decl> )
   * }
   * @param symbol the name of the datatype sort
   * @param ctors the constructor declarations of the datatype sort
   * @return the datatype sort
   */
  public Sort declareDatatype(String symbol, DatatypeConstructorDecl[] ctors)
  {
    long[] pointers = Utils.getPointers(ctors);
    long sortPointer = declareDatatype(pointer, symbol, pointers);
    return new Sort(this, sortPointer);
  }

  private native long declareDatatype(long pointer, String symbol, long[] declPointers);

  /**
   * Declare n-ary function symbol.
   * SMT-LIB:
   * {@code
   *   ( declare-fun <symbol> ( <sort>* ) <sort> )
   * }
   * @param symbol the name of the function
   * @param sorts the sorts of the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  public Term declareFun(String symbol, Sort[] sorts, Sort sort)
  {
    long[] sortPointers = Utils.getPointers(sorts);
    long termPointer = declareFun(pointer, symbol, sortPointers, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long declareFun(
      long pointer, String symbol, long[] sortPointers, long sortPointer);

  /**
   * Declare uninterpreted sort.
   * SMT-LIB:
   * {@code
   *   ( declare-sort <symbol> <numeral> )
   * }
   * @param symbol the name of the sort
   * @param arity the arity of the sort
   * @return the sort
   */
  public Sort declareSort(String symbol, int arity) throws CVC5ApiException
  {
    Utils.validateUnsigned(arity, "arity");
    long sortPointer = declareSort(pointer, symbol, arity);
    return new Sort(this, sortPointer);
  }

  private native long declareSort(long pointer, String symbol, int arity);

  /**
   * Define n-ary function in the current context.
   * SMT-LIB:
   * {@code
   *   ( define-fun <function_def> )
   * }
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @return the function
   */
  public Term defineFun(String symbol, Term[] boundVars, Sort sort, Term term)
  {
    return defineFun(symbol, boundVars, sort, term, false);
  }

  /**
   * Define n-ary function.
   * SMT-LIB:
   * {@code
   *   ( define-fun <function_def> )
   * }
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFun(String symbol, Term[] boundVars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        defineFun(pointer, symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(this, termPointer);
  }

  private native long defineFun(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @return the function
   */
  public Term defineFunRec(String symbol, Term[] boundVars, Sort sort, Term term)
  {
    return defineFunRec(symbol, boundVars, sort, term, false);
  }

  /**
   * Define recursive function.
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFunRec(String symbol, Term[] boundVars, Sort sort, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = defineFunRec(
        pointer, symbol, boundVarPointers, sort.getPointer(), term.getPointer(), global);
    return new Term(this, termPointer);
  }

  private native long defineFunRec(long pointer,
      String symbol,
      long[] boundVarPointers,
      long sortPointer,
      long termPointer,
      boolean global);

  /**
   * Define recursive function in the current context.
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param boundVars the parameters to this function
   * @param term the function body
   * @return the function
   */

  public Term defineFunRec(Term fun, Term[] boundVars, Term term)
  {
    return defineFunRec(fun, boundVars, term, false);
  }

  /**
   * Define recursive function.
   * SMT-LIB:
   * {@code
   * ( define-fun-rec <function_def> )
   * }
   * Create parameter 'fun' with mkConst().
   * @param fun the sorted function
   * @param boundVars the parameters to this function
   * @param term the function body
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
   * @return the function
   */
  public Term defineFunRec(Term fun, Term[] boundVars, Term term, boolean global)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        defineFunRec(pointer, fun.getPointer(), boundVarPointers, term.getPointer(), global);
    return new Term(this, termPointer);
  }

  private native long defineFunRec(
      long pointer, long funPointer, long[] boundVarPointers, long termPointer, boolean global);

  /**
   * Define recursive functions in the current context.
   * SMT-LIB:
   * {@code
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * }
   * Create elements of parameter 'funs' with mkConst().
   * @param funs the sorted functions
   * @param boundVars the list of parameters to the functions
   * @param terms the list of function bodies of the functions
   */
  public void defineFunsRec(Term[] funs, Term[][] boundVars, Term[] terms)
  {
    defineFunsRec(funs, boundVars, terms, false);
  }
  /**
   * Define recursive functions.
   * SMT-LIB:
   * {@code
   *   ( define-funs-rec ( <function_decl>^{n+1} ) ( <term>^{n+1} ) )
   * }
   * Create elements of parameter 'funs' with mkConst().
   * @param funs the sorted functions
   * @param boundVars the list of parameters to the functions
   * @param terms the list of function bodies of the functions
   * @param global determines whether this definition is global (i.e. persists
   *               when popping the context)
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
   * Echo a given string to the given output stream.
   * SMT-LIB:
   * {@code
   * ( echo <std::string> )
   * }
   * @param out the output stream
   * @param str the string to echo
   */
  // TODO: void echo(std::ostream& out, String  str)

  /**
   * Get a list of literals that are entailed by the current set of assertions
   * SMT-LIB:
   * {@code
   * ( get-learned-literals )
   * }
   * @return the list of learned literals
   */
  public Term[] getLearnedLiterals() {
    long[] retPointers = getLearnedLiterals(pointer);
    return Utils.getTerms(this, retPointers);
  }

  private native long[] getLearnedLiterals(long pointer);

  /**
   * Get the list of asserted formulas.
   * SMT-LIB:
   * {@code
   * ( get-assertions )
   * }
   * @return the list of asserted formulas
   */
  public Term[] getAssertions()
  {
    long[] retPointers = getAssertions(pointer);
    return Utils.getTerms(this, retPointers);
  }

  private native long[] getAssertions(long pointer);

  /**
   * Get info from the solver.
   * SMT-LIB: {@code ( get-info <info_flag> ) }
   * @return the info
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
   * @param option the option for which the value is queried
   * @return a string representation of the option value
   */
  public String getOption(String option)
  {
    return getOption(pointer, option);
  }

  private native String getOption(long pointer, String option);

  /**
   * Get all option names that can be used with `setOption`, `getOption` and
   * `getOptionInfo`.
   * @return all option names
   */
  public String[] getOptionNames()
  {
    return getOptionNames(pointer);
  }

  private native String[] getOptionNames(long pointer);

  /**
   * Get some information about the given option. Check the `OptionInfo` class
   * for more details on which information is available.
   * @return information about the given option
   */
  public OptionInfo getOptionInfo(String option)
  {
    long optionPointer = getOptionInfo(pointer, option);
    return new OptionInfo(this, optionPointer);
  }

  private native long getOptionInfo(long pointer, String option);

  /**
   * Get the set of unsat ("failed") assumptions.
   * SMT-LIB:
   * {@code
   * ( get-unsat-assumptions )
   * }
   * Requires to enable option 'produce-unsat-assumptions'.
   * @return the set of unsat assumptions.
   */
  public Term[] getUnsatAssumptions()
  {
    long[] retPointers = getUnsatAssumptions(pointer);
    return Utils.getTerms(this, retPointers);
  }

  private native long[] getUnsatAssumptions(long pointer);

  /**
   * Get the unsatisfiable core.
   * SMT-LIB:
   * {@code
   * (get-unsat-core)
   * }
   * Requires to enable option 'produce-unsat-cores'.
   * @apiNote In contrast to SMT-LIB, the API does not distinguish between
   *          named and unnamed assertions when producing an unsatisfiable
   *          core. Additionally, the API allows this option to be called after
   *          a check with assumptions. A subset of those assumptions may be
   *          included in the unsatisfiable core returned by this method.
   * @return a set of terms representing the unsatisfiable core
   */
  public Term[] getUnsatCore()
  {
    long[] retPointers = getUnsatCore(pointer);
    return Utils.getTerms(this, retPointers);
  }

  private native long[] getUnsatCore(long pointer);

  /**
   * Get a difficulty estimate for an asserted formula. This method is
   * intended to be called immediately after any response to a checkSat.
   *
   * @return a map from (a subset of) the input assertions to a real value that
   * is an estimate of how difficult each assertion was to solve. Unmentioned
   * assertions can be assumed to have zero difficulty.
   */
  public Map<Term, Term> getDifficulty()
  {
    Map<Long, Long> map = getDifficulty(pointer);
    Map<Term, Term> ret = new HashMap<>();
    for (Map.Entry<Long, Long> entry : map.entrySet())
    {
      Term key = new Term(this, entry.getKey());
      Term value = new Term(this, entry.getValue());
      ret.put(key, value);
    }
    return ret;
  }

  private native Map<Long, Long> getDifficulty(long pointer);

  /**
   * Get the refutation proof
   * SMT-LIB:
   * {@code
   * ( get-proof )
   * }
   * Requires to enable option 'produce-proofs'.
   * @return a string representing the proof, according to the value of
   * proof-format-mode.
   */
  public String getProof()
  {
    return getProof(pointer);
  }

  private native String getProof(long pointer);

  /**
   * Get the value of the given term in the current model.
   * SMT-LIB:
   * {@code
   * ( get-value ( <term> ) )
   * }
   * @param term the term for which the value is queried
   * @return the value of the given term
   */
  public Term getValue(Term term)
  {
    long termPointer = getValue(pointer, term.getPointer());
    return new Term(this, termPointer);
  }

  private native long getValue(long pointer, long termPointer);

  /**
   * Get the values of the given terms in the current model.
   * SMT-LIB:
   * {@code
   * ( get-value ( <term>+ ) )
   * }
   * @param terms the terms for which the value is queried
   * @return the values of the given terms
   */
  public Term[] getValue(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    long[] retPointers = getValue(pointer, pointers);
    return Utils.getTerms(this, retPointers);
  }

  private native long[] getValue(long pointer, long[] termPointers);

  /**
   * Get the domain elements of uninterpreted sort s in the current model. The
   * current model interprets s as the finite sort whose domain elements are
   * given in the return value of this method.
   *
   * @param s The uninterpreted sort in question
   * @return the domain elements of s in the current model
   */
  public Term[] getModelDomainElements(Sort s)
  {
    long[] pointers = getModelDomainElements(pointer, s.getPointer());
    return Utils.getTerms(this, pointers);
  }

  private native long[] getModelDomainElements(long pointer, long sortPointer);

  /**
   * This returns false if the model value of free constant v was not essential
   * for showing the satisfiability of the last call to checkSat using the
   * current model. This method will only return false (for any v) if
   * the model-cores option has been set.
   *
   * @param v The term in question
   * @return true if v is a model core symbol
   */
  public boolean isModelCoreSymbol(Term v)
  {
    return isModelCoreSymbol(pointer, v.getPointer());
  }

  private native boolean isModelCoreSymbol(long pointer, long termPointer);

  /**
   * Get the model
   * SMT-LIB:
   * {@code
   * ( get-model )
   * }
   * Requires to enable option 'produce-models'.
   * @param sorts The list of uninterpreted sorts that should be printed in the
   * model.
   * @param vars The list of free constants that should be printed in the
   * model. A subset of these may be printed based on isModelCoreSymbol.
   * @return a string representing the model.
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
   * SMT-LIB:
   * {@code
   * ( get-qe <q> )
   * }
   * Requires a logic that supports quantifier elimination. Currently, the only
   * logics supported by quantifier elimination is LRA and LIA.
   * @param q a quantified formula of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free formula
   * @return a formula ret such that, given the current set of formulas A
   * asserted to this solver:
   *   - ( A ^ q ) and ( A ^ ret ) are equivalent
   *   - ret is quantifier-free formula containing only free variables in
   *     y1...yn.
   */
  public Term getQuantifierElimination(Term q)
  {
    long termPointer = getQuantifierElimination(pointer, q.getPointer());
    return new Term(this, termPointer);
  }

  private native long getQuantifierElimination(long pointer, long qPointer);

  /**
   * Do partial quantifier elimination, which can be used for incrementally
   * computing the result of a quantifier elimination.
   * SMT-LIB:
   * {@code
   * ( get-qe-disjunct <q> )
   * }
   * Requires a logic that supports quantifier elimination. Currently, the only
   * logics supported by quantifier elimination is LRA and LIA.
   * @param q a quantified formula of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free formula
   * @return a formula ret such that, given the current set of formulas A
   * asserted to this solver:
   *   - {@code (A ^ q) => (A ^ ret)} if Q is forall or {@code (A ^ ret) => (A ^ q)} if Q is
   *     exists,
   *   - ret is quantifier-free formula containing only free variables in
   *     y1...yn,
   *   - If Q is exists, let A^Q_n be the formula
   *       {@code A ^ ~ret^Q_1 ^ ... ^ ~ret^Q_n}
   *     where for each i=1,...n, formula ret^Q_i is the result of calling
   *     getQuantifierEliminationDisjunct for q with the set of assertions
   *     {@code A^Q_{i-1}}. Similarly, if Q is forall, then let {@code A^Q_n} be
   *       {@code A ^ ret^Q_1 ^ ... ^ ret^Q_n }
   *     where ret^Q_i is the same as above. In either case, we have
   *     that ret^Q_j will eventually be true or false, for some finite j.
   */
  public Term getQuantifierEliminationDisjunct(Term q)
  {
    long termPointer = getQuantifierEliminationDisjunct(pointer, q.getPointer());
    return new Term(this, termPointer);
  }

  private native long getQuantifierEliminationDisjunct(long pointer, long qPointer);

  /**
   * When using separation logic, this sets the location sort and the
   * datatype sort to the given ones. This method should be invoked exactly
   * once, before any separation logic constraints are provided.
   * @param locSort The location sort of the heap
   * @param dataSort The data sort of the heap
   */
  public void declareSepHeap(Sort locSort, Sort dataSort)
  {
    declareSepHeap(pointer, locSort.getPointer(), dataSort.getPointer());
  }

  private native void declareSepHeap(long pointer, long locSortPointer, long dataSortPointer);

  /**
   * When using separation logic, obtain the term for the heap.
   * @return The term for the heap
   */
  public Term getValueSepHeap()
  {
    long termPointer = getValueSepHeap(pointer);
    return new Term(this, termPointer);
  }

  private native long getValueSepHeap(long pointer);

  /**
   * When using separation logic, obtain the term for nil.
   * @return The term for nil
   */
  public Term getValueSepNil()
  {
    long termPointer = getValueSepNil(pointer);
    return new Term(this, termPointer);
  }

  private native long getValueSepNil(long pointer);

  /**
   * Declare a symbolic pool of terms with the given initial value.
   * SMT-LIB:
   * {@code
   * ( declare-pool <symbol> <sort> ( <term>* ) )
   * }
   * @param symbol The name of the pool
   * @param sort The sort of the elements of the pool.
   * @param initValue The initial value of the pool
   */
  public Term declarePool(String symbol, Sort sort, Term[] initValue)
  {
    long[] termPointers = Utils.getPointers(initValue);
    long termPointer = declarePool(pointer, symbol, sort.getPointer(), termPointers);
    return new Term(this, termPointer);
  }

  private native long declarePool(
      long pointer, String symbol, long sortPointer, long[] termPointers);

  /**
   * Pop a level from the assertion stack.
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   */
  public void pop() throws CVC5ApiException
  {
    pop(1);
  }

  /**
   * Pop (a) level(s) from the assertion stack.
   * SMT-LIB:
   * {@code
   * ( pop <numeral> )
   * }
   * @param nscopes the number of levels to pop
   */
  public void pop(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    pop(pointer, nscopes);
  }

  private native void pop(long pointer, int nscopes);

  /**
   * Get an interpolant
   * SMT-LIB:
   * {@code
   * ( get-interpol <conj> )
   * }
   * Requires 'produce-interpols' to be set to a mode different from 'none'.
   * @param conj the conjecture term
   * @param output a Term I such that {@code A->I} and {@code I->B} are valid, where A is the
   *        current set of assertions and B is given in the input by conj.
   * @return true if it gets I successfully, false otherwise.
   */
  public boolean getInterpolant(Term conj, Term output)
  {
    return getInterpolant(pointer, conj.getPointer(), output.getPointer());
  }

  private native boolean getInterpolant(long pointer, long conjPointer, long outputPointer);

  /**
   * Get an interpolant
   * SMT-LIB:
   * {@code
   * ( get-interpol <conj> <g> )
   * }
   * Requires 'produce-interpols' to be set to a mode different from 'none'.
   * @param conj the conjecture term
   * @param grammar the grammar for the interpolant I
   * @param output a Term I such that {@code A->I} and {@code I->B} are valid, where A is the
   *        current set of assertions and B is given in the input by conj.
   * @return true if it gets I successfully, false otherwise.
   */
  public boolean getInterpolant(Term conj, Grammar grammar, Term output)
  {
    return getInterpolant(pointer, conj.getPointer(), grammar.getPointer(), output.getPointer());
  }

  private native boolean getInterpolant(
      long pointer, long conjPointer, long grammarPointer, long outputPointer);

  /**
   * Get the next interpolant. Can only be called immediately after a successful
   * call to get-interpol or get-interpol-next. Is guaranteed to produce a
   * syntactically different interpolant wrt the last returned interpolant if
   * successful.
   *
   * SMT-LIB:
   *
   * \verbatim embed:rst:leading-asterisk
   * .. code:: smtlib
   *
   *     (get-interpol-next)
   *
   * Requires to enable incremental mode, and option 'produce-interpols' to be
   * set to a mode different from 'none'.
   * \endverbatim
   *
   * @param output a Term I such that {@code A->I} and {@code I->B} are valid,
   *        where A is the current set of assertions and B is given in the input
   *        by conj on the last call to getInterpolant.
   * @return true if it gets interpolant @f$C@f$ successfully, false otherwise
   */
  public boolean getInterpolantNext(Term output)
  {
    return getInterpolantNext(pointer, output.getPointer());
  }

  private native boolean getInterpolantNext(long pointer, long outputPointer);

  /**
   * Get an abduct.
   * SMT-LIB:
   * {@code
   * ( get-abduct <conj> )
   * }
   * Requires enabling option 'produce-abducts'
   * @param conj the conjecture term
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj
   * @return true if it gets C successfully, false otherwise
   */
  public boolean getAbduct(Term conj, Term output)
  {
    return getAbduct(pointer, conj.getPointer(), output.getPointer());
  }

  private native boolean getAbduct(long pointer, long conjPointer, long outputPointer);
  /**
   * Get an abduct.
   * SMT-LIB:
   * {@code
   * ( get-abduct <conj> <g> )
   * }
   * Requires enabling option 'produce-abducts'
   * @param conj the conjecture term
   * @param grammar the grammar for the abduct C
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj
   * @return true if it gets C successfully, false otherwise
   */
  public boolean getAbduct(Term conj, Grammar grammar, Term output)
  {
    return getAbduct(pointer, conj.getPointer(), grammar.getPointer(), output.getPointer());
  }

  private native boolean getAbduct(
      long pointer, long conjPointer, long grammarPointer, long outputPointer);

  /**
   * Get the next abduct. Can only be called immediately after a successful
   * call to get-abduct or get-abduct-next. Is guaranteed to produce a
   * syntactically different abduct wrt the last returned abduct if successful.
   * SMT-LIB:
   * {@code
   * ( get-abduct-next )
   * }
   * Requires enabling incremental mode and option 'produce-abducts'
   * @param output a term C such that A^C is satisfiable, and A^~B^C is
   *        unsatisfiable, where A is the current set of assertions and B is
   *        given in the input by conj in the last call to getAbduct.
   * @return true if it gets C successfully, false otherwise
   */
  public boolean getAbductNext(Term output) {
    return getAbductNext(pointer, output.getPointer());
  }

  private native boolean getAbductNext(long pointer, long outputPointer);

  /**
   * Block the current model. Can be called only if immediately preceded by a
   * SAT or INVALID query.
   * SMT-LIB:
   * {@code
   * ( block-model )
   * }
   * Requires enabling 'produce-models' option and setting 'block-models' option
   * to a mode other than "none".
   */
  public void blockModel()
  {
    blockModel(pointer);
  }

  private native void blockModel(long pointer);

  /**
   * Block the current model values of (at least) the values in terms. Can be
   * called only if immediately preceded by a SAT or NOT_ENTAILED query.
   * SMT-LIB:
   * {@code
   * ( block-model-values ( <terms>+ ) )
   * }
   * Requires enabling 'produce-models' option.
   */
  public void blockModelValues(Term[] terms)
  {
    long[] pointers = Utils.getPointers(terms);
    blockModelValues(pointer, pointers);
  }

  private native void blockModelValues(long pointer, long[] termPointers);

  /**
   * Print all instantiations made by the quantifiers module.
   * @param out the output stream
   */
  // TODO: void printInstantiations(std::ostream& out)

  /**
   * Push a level to the assertion stack.
   * SMT-LIB:
   * {@code
   * ( push <numeral> )
   * }
   */
  public void push() throws CVC5ApiException
  {
    push(1);
  }

  /**
   * Push (a) level(s) to the assertion stack.
   * SMT-LIB:
   * {@code
   * ( push <numeral> )
   * }
   * @param nscopes the number of levels to push
   */
  public void push(int nscopes) throws CVC5ApiException
  {
    Utils.validateUnsigned(nscopes, "nscopes");
    push(pointer, nscopes);
  }

  private native void push(long pointer, int nscopes);

  /**
   * Remove all assertions.
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
   * SMT-LIB:
   * {@code
   * ( set-info <attribute> )
   * }
   * @param keyword the info flag
   * @param value the value of the info flag
   */
  public void setInfo(String keyword, String value) throws CVC5ApiException
  {
    setInfo(pointer, keyword, value);
  }

  private native void setInfo(long pointer, String keyword, String value) throws CVC5ApiException;

  /**
   * Set logic.
   * SMT-LIB:
   * {@code
   * ( set-logic <symbol> )
   * }
   * @param logic the logic to set
   */
  public void setLogic(String logic) throws CVC5ApiException
  {
    setLogic(pointer, logic);
  }

  private native void setLogic(long pointer, String logic) throws CVC5ApiException;

  /**
   * Set option.
   * SMT-LIB:
   * {@code
   *   ( set-option <option> )
   * }
   * @param option the option name
   * @param value the option value
   */
  public void setOption(String option, String value)
  {
    setOption(pointer, option, value);
  }

  private native void setOption(long pointer, String option, String value);

  /**
   * If needed, convert this term to a given sort.
   *
   * @apiNote The sort of the term must be convertible into the target sort.
   *          Currently only Int to Real conversions are supported.
   * @param t the term
   * @param s the target sort
   * @return the term wrapped into a sort conversion if needed
   */
  public Term ensureTermSort(Term t, Sort s)
  {
    long termPointer = ensureTermSort(pointer, t.getPointer(), s.getPointer());
    return new Term(this, termPointer);
  }

  private native long ensureTermSort(long pointer, long termPointer, long sortPointer);

  /**
   * Append \p symbol to the current list of universal variables.
   * @param sort the sort of the universal variable
   * @return the universal variable
   */
  public Term mkSygusVar(Sort sort)
  {
    return mkSygusVar(sort, "");
  }
  /**
   * Append \p symbol to the current list of universal variables.
   * SyGuS v2:
   * {@code
   *   ( declare-var <symbol> <sort> )
   * }
   * @param sort the sort of the universal variable
   * @param symbol the name of the universal variable
   * @return the universal variable
   */
  public Term mkSygusVar(Sort sort, String symbol)
  {
    long termPointer = mkSygusVar(pointer, sort.getPointer(), symbol);
    return new Term(this, termPointer);
  }

  private native long mkSygusVar(long pointer, long sortPointer, String symbol);

  /**
   * Create a Sygus grammar. The first non-terminal is treated as the starting
   * non-terminal, so the order of non-terminals matters.
   *
   * @param boundVars the parameters to corresponding synth-fun/synth-inv
   * @param ntSymbols the pre-declaration of the non-terminal symbols
   * @return the grammar
   */
  public Grammar mkSygusGrammar(Term[] boundVars, Term[] ntSymbols)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long[] ntSymbolPointers = Utils.getPointers(ntSymbols);
    long grammarPointer = mkSygusGrammar(pointer, boundVarPointers, ntSymbolPointers);
    return new Grammar(this, grammarPointer);
  }

  private native long mkSygusGrammar(
      long pointer, long[] boundVarPointers, long[] ntSymbolPointers);

  /**
   * Synthesize n-ary function.
   * SyGuS v2:
   * {@code
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> )
   * }
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @return the function
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthFun(pointer, symbol, boundVarPointers, sort.getPointer());
    return new Term(this, termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer);

  /**
   * Synthesize n-ary function following specified syntactic constraints.
   * SyGuS v2:
   * {@code
   *   ( synth-fun <symbol> ( <boundVars>* ) <sort> <g> )
   * }
   * @param symbol the name of the function
   * @param boundVars the parameters to this function
   * @param sort the sort of the return value of this function
   * @param grammar the syntactic constraints
   * @return the function
   */
  public Term synthFun(String symbol, Term[] boundVars, Sort sort, Grammar grammar)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer =
        synthFun(pointer, symbol, boundVarPointers, sort.getPointer(), grammar.getPointer());
    return new Term(this, termPointer);
  }

  private native long synthFun(
      long pointer, String symbol, long[] boundVarPointers, long sortPointer, long grammarPointer);

  /**
   * Synthesize invariant.
   * SyGuS v2:
   * {@code
   *   ( synth-inv <symbol> ( <boundVars>* ) )
   * }
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @return the invariant
   */
  public Term synthInv(String symbol, Term[] boundVars)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthInv(pointer, symbol, boundVarPointers);
    return new Term(this, termPointer);
  }

  private native long synthInv(long pointer, String symbol, long[] boundVarPointers);

  /**
   * Synthesize invariant following specified syntactic constraints.
   * SyGuS v2:
   * {@code
   *   ( synth-inv <symbol> ( <boundVars>* ) <g> )
   * }
   * @param symbol the name of the invariant
   * @param boundVars the parameters to this invariant
   * @param grammar the syntactic constraints
   * @return the invariant
   */
  public Term synthInv(String symbol, Term[] boundVars, Grammar grammar)
  {
    long[] boundVarPointers = Utils.getPointers(boundVars);
    long termPointer = synthInv(pointer, symbol, boundVarPointers, grammar.getPointer());
    return new Term(this, termPointer);
  }

  private native long synthInv(
      long pointer, String symbol, long[] boundVarPointers, long grammarPointer);

  /**
   * Add a forumla to the set of Sygus constraints.
   * SyGuS v2:
   * {@code
   *   ( constraint <term> )
   * }
   * @param term the formula to add as a constraint
   */
  public void addSygusConstraint(Term term)
  {
    addSygusConstraint(pointer, term.getPointer());
  }

  private native void addSygusConstraint(long pointer, long termPointer);

  /**
   * Add a forumla to the set of Sygus assumptions.
   * SyGuS v2:
   * {@code
   *   ( assume <term> )
   * }
   * @param term the formula to add as an assumption
   */
  public void addSygusAssume(Term term)
  {
    addSygusAssume(pointer, term.getPointer());
  }

  private native void addSygusAssume(long pointer, long termPointer);

  /**
   * Add a set of Sygus constraints to the current state that correspond to an
   * invariant synthesis problem.
   * SyGuS v2:
   * {@code
   *   ( inv-constraint <inv> <pre> <trans> <post> )
   * }
   * @param inv the function-to-synthesize
   * @param pre the pre-condition
   * @param trans the transition relation
   * @param post the post-condition
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
   * SyGuS v2:
   * {@code
   *   ( check-synth )
   * }
   * @return the result of the check, which is unsat if the check succeeded,
   * in which case solutions are available via getSynthSolutions.
   */
  public Result checkSynth()
  {
    long resultPointer = checkSynth(pointer);
    return new Result(this, resultPointer);
  }

  private native long checkSynth(long pointer);

  /**
   * Try to find a next solution for the synthesis conjecture corresponding to
   * the current list of functions-to-synthesize, universal variables and
   * constraints. Must be called immediately after a successful call to
   * check-synth or check-synth-next. Requires incremental mode.
   * SyGuS v2:
   * {@code
   *   ( check-synth-next )
   * }
   * @return the result of the check, which is UNSAT if the check succeeded,
   * in which case solutions are available via getSynthSolutions.
   */
  public Result checkSynthNext()
  {
    long resultPointer = checkSynthNext(pointer);
    return new Result(this, resultPointer);
  }

  private native long checkSynthNext(long pointer);

  /**
   * Get the synthesis solution of the given term. This method should be called
   * immediately after the solver answers unsat for sygus input.
   * @param term the term for which the synthesis solution is queried
   * @return the synthesis solution of the given term
   */
  public Term getSynthSolution(Term term)
  {
    long termPointer = getSynthSolution(pointer, term.getPointer());
    return new Term(this, termPointer);
  }

  private native long getSynthSolution(long pointer, long termPointer);

  /**
   * Get the synthesis solutions of the given terms. This method should be
   * called immediately after the solver answers unsat for sygus input.
   * @param terms the terms for which the synthesis solutions is queried
   * @return the synthesis solutions of the given terms
   */
  public Term[] getSynthSolutions(Term[] terms)
  {
    long[] termPointers = Utils.getPointers(terms);
    long[] retPointers = getSynthSolutions(pointer, termPointers);
    return Utils.getTerms(this, retPointers);
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
    return new Statistics(this, statisticsPointer);
  }

  private native long getStatistics(long pointer);

  /**
   * @return null term
   */
  public Term getNullTerm()
  {
    long termPointer = getNullTerm(pointer);
    return new Term(this, termPointer);
  }

  private native long getNullTerm(long pointer);

  /**
   * @return null result
   */
  public Result getNullResult()
  {
    long resultPointer = getNullResult(pointer);
    return new Result(this, resultPointer);
  }

  private native long getNullResult(long pointer);

  /**
   * @return null op
   */
  public Op getNullOp()
  {
    long opPointer = getNullOp(pointer);
    return new Op(this, opPointer);
  }

  private native long getNullOp(long pointer);

  /**
   * @return null op
   */
  public DatatypeDecl getNullDatatypeDecl()
  {
    long declPointer = getNullDatatypeDecl(pointer);
    return new DatatypeDecl(this, declPointer);
  }

  private native long getNullDatatypeDecl(long pointer);
}
