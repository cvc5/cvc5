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

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;

public class Term extends AbstractPointer implements Comparable<Term>, Iterable<Term>
{
  // region construction and destruction
  Term(Solver solver, long pointer)
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
   * Syntactic equality operator.
   * Return true if both terms are syntactically identical.
   * Both terms must belong to the same solver object.
   *
   * @param t the term to compare to for equality
   * @return true if the terms are equal
   */
  @Override public boolean equals(Object t)
  {
    if (this == t)
      return true;
    if (t == null || getClass() != t.getClass())
      return false;
    Term term = (Term) t;
    if (this.pointer == term.pointer)
    {
      return true;
    }
    return equals(pointer, term.getPointer());
  }

  private native boolean equals(long pointer1, long pointer2);

  /**
   * Comparison for ordering on terms.
   *
   * @param t the term to compare to
   * @return a negative integer, zero, or a positive integer as this term
   * is less than, equal to, or greater than the specified term.
   */
  @Override public int compareTo(Term t)
  {
    return this.compareTo(pointer, t.getPointer());
  }

  private native int compareTo(long pointer1, long pointer2);

  /**
   * @return the number of children of this term
   */
  public int getNumChildren()
  {
    return getNumChildren(pointer);
  }

  private native int getNumChildren(long pointer);

  /**
   * Get the child term at a given index.
   *
   * @param index the index of the child term to return
   * @return the child term with the given index
   */
  public Term getChild(int index) throws CVC5ApiException
  {
    Utils.validateUnsigned(index, "index");
    long termPointer = getChild(pointer, index);
    return new Term(solver, termPointer);
  }

  private native long getChild(long pointer, int index);

  /**
   * @return the id of this term
   */
  public long getId()
  {
    return getId(pointer);
  }

  private native long getId(long pointer);

  /**
   * @return the kind of this term
   */
  public Kind getKind() throws CVC5ApiException
  {
    int value = getKind(pointer);
    return Kind.fromInt(value);
  }

  private native int getKind(long pointer);

  /**
   * @return the sort of this term
   */
  public Sort getSort()
  {
    long sortPointer = getSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getSort(long pointer);

  /**
   * @return the result of replacing 'term' by 'replacement' in this term
   */
  public Term substitute(Term term, Term replacement)
  {
    long termPointer = substitute(pointer, term.getPointer(), replacement.getPointer());
    return new Term(solver, termPointer);
  }

  private native long substitute(long pointer, long termPointer, long replacementPointer);

  /**
   * @return the result of simultaneously replacing 'terms' by 'replacements'
   * in this term
   */
  public Term substitute(List<Term> terms, List<Term> replacements)
  {
    return substitute(terms.toArray(new Term[0]), replacements.toArray(new Term[0]));
  }

  /**
   * @return the result of simultaneously replacing 'terms' by 'replacements'
   * in this term
   */
  public Term substitute(Term[] terms, Term[] replacements)
  {
    long[] termPointers = new long[terms.length];
    for (int i = 0; i < termPointers.length; i++)
    {
      termPointers[i] = terms[i].getPointer();
    }
    long[] replacementPointers = new long[replacements.length];
    for (int i = 0; i < replacements.length; i++)
    {
      replacementPointers[i] = replacements[i].getPointer();
    }

    long termPointer = substitute(pointer, termPointers, replacementPointers);
    return new Term(solver, termPointer);
  }

  private native long substitute(long pointer, long[] termPointers, long[] replacementPointers);

  /**
   * @return true iff this term has an operator
   */
  public boolean hasOp()
  {
    return hasOp(pointer);
  }

  private native boolean hasOp(long pointer);

  /**
   * @return the Op used to create this term
   * Note: This is safe to call when hasOp() returns true.
   */
  public Op getOp()
  {
    long opPointer = getOp(pointer);
    return new Op(solver, opPointer);
  }

  private native long getOp(long pointer);

  /**
   * @return true if the term has a symbol.
   */
  public boolean hasSymbol()
  {
    return hasSymbol(pointer);
  }

  private native boolean hasSymbol(long pointer);

  /**
   * Asserts hasSymbol().
   * @return the raw symbol of the term.
   */
  public String getSymbol()
  {
    return getSymbol(pointer);
  }

  private native String getSymbol(long pointer);

  /**
   * @return true if this Term is a null term
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Boolean negation.
   *
   * @return the Boolean negation of this term
   */
  public Term notTerm()
  {
    long termPointer = notTerm(pointer);
    return new Term(solver, termPointer);
  }

  private native long notTerm(long pointer);

  /**
   * Boolean and.
   *
   * @param t a Boolean term
   * @return the conjunction of this term and the given term
   */
  public Term andTerm(Term t)
  {
    long termPointer = andTerm(pointer, t.getPointer());
    return new Term(solver, termPointer);
  }

  private native long andTerm(long pointer, long termPointer);

  /**
   * Boolean or.
   *
   * @param t a Boolean term
   * @return the disjunction of this term and the given term
   */
  public Term orTerm(Term t)
  {
    long termPointer = orTerm(pointer, t.getPointer());
    return new Term(solver, termPointer);
  }

  private native long orTerm(long pointer, long termPointer);

  /**
   * Boolean exclusive or.
   *
   * @param t a Boolean term
   * @return the exclusive disjunction of this term and the given term
   */
  public Term xorTerm(Term t)
  {
    long termPointer = xorTerm(pointer, t.getPointer());
    return new Term(solver, termPointer);
  }

  private native long xorTerm(long pointer, long termPointer);

  /**
   * Equality.
   *
   * @param t a Boolean term
   * @return the Boolean equivalence of this term and the given term
   */
  public Term eqTerm(Term t)
  {
    long termPointer = eqTerm(pointer, t.getPointer());
    return new Term(solver, termPointer);
  }

  private native long eqTerm(long pointer, long termPointer);

  /**
   * Boolean implication.
   *
   * @param t a Boolean term
   * @return the implication of this term and the given term
   */
  public Term impTerm(Term t)
  {
    long termPointer = impTerm(pointer, t.getPointer());
    return new Term(solver, termPointer);
  }

  private native long impTerm(long pointer, long termPointer);

  /**
   * If-then-else with this term as the Boolean condition.
   *
   * @param thenTerm the 'then' term
   * @param elseTerm the 'else' term
   * @return the if-then-else term with this term as the Boolean condition
   */
  public Term iteTerm(Term thenTerm, Term elseTerm)
  {
    long termPointer = iteTerm(pointer, thenTerm.getPointer(), elseTerm.getPointer());
    return new Term(solver, termPointer);
  }

  private native long iteTerm(long pointer, long thenPointer, long elsePointer);

  /**
   * @return a string representation of this term.
   */
  protected native String toString(long pointer);

  /**
   * @return true if the term is an integer value.
   */
  public boolean isIntegerValue()
  {
    return isIntegerValue(pointer);
  }

  private native boolean isIntegerValue(long pointer);

  /**
   * Asserts isIntegerValue().
   * @return the integer represented by this term.
   */
  public BigInteger getIntegerValue()
  {
    return new BigInteger(getIntegerValue(pointer));
  }

  private native String getIntegerValue(long pointer);

  /**
   * @return true if the term is a string constant.
   */
  public boolean isStringValue()
  {
    return isStringValue(pointer);
  }

  private native boolean isStringValue(long pointer);

  /**
   * @return the stored string constant.
   * <p>
   * Note: This method is not to be confused with toString() which returns the
   * term in some string representation, whatever data it may hold.
   * Asserts isString().
   */
  public String getStringValue()
  {
    return getStringValue(pointer);
  }

  private native String getStringValue(long pointer);

  /**
   * @return true if the term is a rational value.
   */
  public boolean isRealValue()
  {
    return isRealValue(pointer);
  }

  private native boolean isRealValue(long pointer);

  /**
   * Asserts isRealValue().
   * @return the representation of a rational value as a pair of its numerator
   * and denominator.
   */
  public Pair<BigInteger, BigInteger> getRealValue()
  {
    String rational = getRealValue(pointer);
    return Utils.getRational(rational);
  }

  private native String getRealValue(long pointer);

  /**
   * @return true if the term is a constant array.
   */
  public boolean isConstArray()
  {
    return isConstArray(pointer);
  }

  private native boolean isConstArray(long pointer);

  /**
   * Asserts isConstArray().
   * @return the base (element stored at all indices) of a constant array
   */
  public Term getConstArrayBase()
  {
    long termPointer = getConstArrayBase(pointer);
    return new Term(solver, termPointer);
  }

  private native long getConstArrayBase(long pointer);

  /**
   * @return true if the term is a Boolean value.
   */
  public boolean isBooleanValue()
  {
    return isBooleanValue(pointer);
  }

  private native boolean isBooleanValue(long pointer);
  /**
   * Asserts isBooleanValue().
   * @return the representation of a Boolean value as a native Boolean value.
   */
  public boolean getBooleanValue()
  {
    return getBooleanValue(pointer);
  }

  private native boolean getBooleanValue(long pointer);

  /**
   * @return true if the term is a bit-vector value.
   */
  public boolean isBitVectorValue()
  {
    return isBitVectorValue(pointer);
  }

  private native boolean isBitVectorValue(long pointer);

  /**
   * Asserts isBitVectorValue().
   * @return the representation of a bit-vector value in bit string representation.
   */
  public String getBitVectorValue() throws CVC5ApiException
  {
    return getBitVectorValue(2);
  }

  /**
   * Asserts isBitVectorValue().
   * @return the representation of a bit-vector value in string representation.
   * Supported bases are 2 (bit string), 10 (decimal string) or 16 (hexadecimal
   * string).
   */
  public String getBitVectorValue(int base) throws CVC5ApiException
  {
    Utils.validateUnsigned(base, "base");
    return getBitVectorValue(pointer, base);
  }

  private native String getBitVectorValue(long pointer, int base);

  /**
   * @return true if the term is an abstract value.
   */
  public boolean isAbstractValue()
  {
    return isAbstractValue(pointer);
  }

  private native boolean isAbstractValue(long pointer);

  /**
   * Asserts isAbstractValue().
   * @return the representation of an abstract value as a string.
   */
  public String getAbstractValue()
  {
    return getAbstractValue(pointer);
  }

  private native String getAbstractValue(long pointer);

  /**
   * @return true if the term is a tuple value.
   */
  public boolean isTupleValue()
  {
    return isTupleValue(pointer);
  }

  private native boolean isTupleValue(long pointer);

  /**
   * Asserts isTupleValue().
   * @return the representation of a tuple value as a vector of terms.
   */
  public Term[] getTupleValue()
  {
    long[] termPointers = getTupleValue(pointer);
    return Utils.getTerms(solver, termPointers);
  }

  private native long[] getTupleValue(long pointer);

  /**
   * @return true if the term is the floating-point value for positive zero.
   */
  public boolean isFloatingPointPosZero()
  {
    return isFloatingPointPosZero(pointer);
  }

  private native boolean isFloatingPointPosZero(long pointer);
  /**
   * @return true if the term is the floating-point value for negative zero.
   */
  public boolean isFloatingPointNegZero()
  {
    return isFloatingPointNegZero(pointer);
  }

  private native boolean isFloatingPointNegZero(long pointer);
  /**
   * @return true if the term is the floating-point value for positive
   * infinity.
   */
  public boolean isFloatingPointPosInf()
  {
    return isFloatingPointPosInf(pointer);
  }

  private native boolean isFloatingPointPosInf(long pointer);
  /**
   * @return true if the term is the floating-point value for negative
   * infinity.
   */
  public boolean isFloatingPointNegInf()
  {
    return isFloatingPointNegInf(pointer);
  }

  private native boolean isFloatingPointNegInf(long pointer);
  /**
   * @return true if the term is the floating-point value for not a number.
   */
  public boolean isFloatingPointNaN()
  {
    return isFloatingPointNaN(pointer);
  }

  private native boolean isFloatingPointNaN(long pointer);
  /**
   * @return true if the term is a floating-point value.
   */
  public boolean isFloatingPointValue()
  {
    return isFloatingPointValue(pointer);
  }

  private native boolean isFloatingPointValue(long pointer);
  /**
   * Asserts isFloatingPointValue().
   * @return the representation of a floating-point value as a tuple of the
   * exponent width, the significand width and a bit-vector value.
   */
  public Triplet<Long, Long, Term> getFloatingPointValue()
  {
    Triplet<Long, Long, Long> triplet = getFloatingPointValue(pointer);
    return new Triplet(triplet.first, triplet.second, new Term(solver, triplet.third));
  }

  private native Triplet<Long, Long, Long> getFloatingPointValue(long pointer);

  /**
   * @return true if the term is a set value.
   */
  public boolean isSetValue()
  {
    return isSetValue(pointer);
  }

  private native boolean isSetValue(long pointer);
  /**
   * Asserts isSetValue().
   * @return the representation of a set value as a set of terms.
   */
  public Set<Term> getSetValue()
  {
    long[] termPointers = getSetValue(pointer);
    Term[] terms = Utils.getTerms(solver, termPointers);
    return new HashSet<Term>(Arrays.asList(terms));
  }

  private native long[] getSetValue(long pointer);

  /**
   * @return true if the term is a sequence value.
   */
  public boolean isSequenceValue()
  {
    return isSequenceValue(pointer);
  }

  private native boolean isSequenceValue(long pointer);

  /**
   * Asserts isSequenceValue().
   * Note that it is usually necessary for sequences to call
   * `Solver::simplify()` to turn a sequence that is constructed by, e.g.,
   * concatenation of unit sequences, into a sequence value.
   * @return the representation of a sequence value as a vector of terms.
   */
  public Term[] getSequenceValue()
  {
    long[] termPointers = getSequenceValue(pointer);
    return Utils.getTerms(solver, termPointers);
  }

  private native long[] getSequenceValue(long pointer);

  /**
   * @return true if the term is a value from an uninterpreted sort.
   */
  public boolean isUninterpretedValue()
  {
    return isUninterpretedValue(pointer);
  }

  private native boolean isUninterpretedValue(long pointer);

  /**
  boolean @return()
   * Asserts isUninterpretedValue().
   * @return the representation of an uninterpreted value as a pair of its
  sort and its
   * index.
   */
  public Pair<Sort, Integer> getUninterpretedValue()
  {
    Pair<Long, Integer> pair = getUninterpretedValue(pointer);
    Sort sort = new Sort(solver, pair.first);
    return new Pair<Sort, Integer>(sort, pair.second);
  }

  private native Pair<Long, Integer> getUninterpretedValue(long pointer);

  public class ConstIterator implements Iterator<Term>
  {
    private int currentIndex;
    private int size;

    public ConstIterator()
    {
      currentIndex = -1;
      size = getNumChildren();
    }

    @Override public boolean hasNext()
    {
      return currentIndex < size - 1;
    }

    @Override public Term next()
    {
      if (currentIndex >= size - 1)
      {
        throw new NoSuchElementException();
      }
      currentIndex++;
      try
      {
        return getChild(currentIndex);
      }
      catch (CVC5ApiException e)
      {
        e.printStackTrace();
        throw new RuntimeException(e.getMessage());
      }
    }
  }

  @Override public Iterator<Term> iterator()
  {
    return new ConstIterator();
  }
}
