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

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * A cvc5 Term.
 */
public class Term extends AbstractPointer implements Comparable<Term>, Iterable<Term>
{
  /**
   * Null term
   */
  public Term()
  {
    super(getNullTerm());
  }

  private static native long getNullTerm();

  Term(long pointer)
  {
    super(pointer);
  }

  protected native void deletePointer(long pointer);

  public long getPointer()
  {
    return pointer;
  }

  /**
   * Syntactic equality operator.
   * Return true if both terms are syntactically identical.
   * Both terms must belong to the same solver object.
   *
   * @param t The term to compare to for equality.
   * @return True if the terms are equal.
   */
  @Override
  public boolean equals(Object t)
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
   * @param t The term to compare to.
   * @return A negative integer, zero, or a positive integer as this term.
   * is less than, equal to, or greater than the specified term.
   */
  @Override
  public int compareTo(Term t)
  {
    return this.compareTo(pointer, t.getPointer());
  }

  private native int compareTo(long pointer1, long pointer2);

  /**
   * @return The number of children of this term.
   */
  public int getNumChildren()
  {
    return getNumChildren(pointer);
  }

  private native int getNumChildren(long pointer);

  /**
   * Get the child term at a given index.
   *
   * @param index The index of the child term to return.
   * @return The child term with the given index.
   */
  public Term getChild(int index) throws CVC5ApiException
  {
    Utils.validateUnsigned(index, "index");
    long termPointer = getChild(pointer, index);
    return new Term(termPointer);
  }

  private native long getChild(long pointer, int index);

  /**
   * @return The id of this term.
   */
  public long getId()
  {
    return getId(pointer);
  }

  private native long getId(long pointer);

  /**
   * @return The kind of this term.
   */
  public Kind getKind() throws CVC5ApiException
  {
    int value = getKind(pointer);
    return Kind.fromInt(value);
  }

  private native int getKind(long pointer);

  /**
   * @return The sort of this term.
   */
  public Sort getSort()
  {
    long sortPointer = getSort(pointer);
    return new Sort(sortPointer);
  }

  private native long getSort(long pointer);

  /**
   * Replace {@code term} with {@code replacement} in this term.
   *
   * @return The result of replacing {@code term} with {@code replacement} in
   *         this term.
   *
   * @api.note This replacement is applied during a pre-order traversal and
   *           only once (it is not run until fixed point).
   */
  public Term substitute(Term term, Term replacement)
  {
    long termPointer = substitute(pointer, term.getPointer(), replacement.getPointer());
    return new Term(termPointer);
  }

  private native long substitute(long pointer, long termPointer, long replacementPointer);

  /**
   * Simultaneously replace {@code terms} with {@code replacements} in this
   * term.
   *
   * In the case that terms contains duplicates, the replacement earliest in
   * the vector takes priority. For example, calling substitute on
   * {@code f(x,y)} with {@code terms = { x, z }},
   * {@code replacements = { g(z), w }} results in the term
   * {@code f(g(z),y)}.
   *
   * @api.note This replacement is applied during a pre-order traversal and
   *           only once (it is not run until fixed point).
   *
   * @return The result of simultaneously replacing {@code terms} with
   *         {@code replacements} in this term.
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
    return new Term(termPointer);
  }

  private native long substitute(long pointer, long[] termPointers, long[] replacementPointers);

  /**
   * @return True iff this term has an operator.
   */
  public boolean hasOp()
  {
    return hasOp(pointer);
  }

  private native boolean hasOp(long pointer);

  /**
   * @return The Op used to create this term.
   * @api.note This is safe to call when {@link Term#hasOp()} returns true.
   */
  public Op getOp()
  {
    long opPointer = getOp(pointer);
    return new Op(opPointer);
  }

  private native long getOp(long pointer);

  /**
   * @return True if the term has a symbol.
   */
  public boolean hasSymbol()
  {
    return hasSymbol(pointer);
  }

  private native boolean hasSymbol(long pointer);

  /**
   * Asserts hasSymbol().
   * @return The raw symbol of the term.
   */
  public String getSymbol()
  {
    return getSymbol(pointer);
  }

  private native String getSymbol(long pointer);

  /**
   * @return True if this Term is a null term.
   */
  public boolean isNull()
  {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Boolean negation.
   *
   * @return The Boolean negation of this term.
   */
  public Term notTerm()
  {
    long termPointer = notTerm(pointer);
    return new Term(termPointer);
  }

  private native long notTerm(long pointer);

  /**
   * Boolean and.
   *
   * @param t A Boolean term.
   * @return The conjunction of this term and the given term.
   */
  public Term andTerm(Term t)
  {
    long termPointer = andTerm(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long andTerm(long pointer, long termPointer);

  /**
   * Boolean or.
   *
   * @param t A Boolean term.
   * @return The disjunction of this term and the given term.
   */
  public Term orTerm(Term t)
  {
    long termPointer = orTerm(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long orTerm(long pointer, long termPointer);

  /**
   * Boolean exclusive or.
   *
   * @param t A Boolean term.
   * @return The exclusive disjunction of this term and the given term.
   */
  public Term xorTerm(Term t)
  {
    long termPointer = xorTerm(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long xorTerm(long pointer, long termPointer);

  /**
   * Equality.
   *
   * @param t A Boolean term.
   * @return The Boolean equivalence of this term and the given term.
   */
  public Term eqTerm(Term t)
  {
    long termPointer = eqTerm(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long eqTerm(long pointer, long termPointer);

  /**
   * Boolean implication.
   *
   * @param t A Boolean term.
   * @return The implication of this term and the given term.
   */
  public Term impTerm(Term t)
  {
    long termPointer = impTerm(pointer, t.getPointer());
    return new Term(termPointer);
  }

  private native long impTerm(long pointer, long termPointer);

  /**
   * If-then-else with this term as the Boolean condition.
   *
   * @param thenTerm The 'then' term.
   * @param elseTerm The 'else' term.
   * @return The if-then-else term with this term as the Boolean condition.
   */
  public Term iteTerm(Term thenTerm, Term elseTerm)
  {
    long termPointer = iteTerm(pointer, thenTerm.getPointer(), elseTerm.getPointer());
    return new Term(termPointer);
  }

  private native long iteTerm(long pointer, long thenPointer, long elsePointer);

  /**
   * @return A string representation of this term.
   */
  protected native String toString(long pointer);

  /**
   * Get integer or real value sign. Must be called on integer or real values,
   * or otherwise an exception is thrown.
   * @return 0 if this term is zero, -1 if this term is a negative real or
   *         integer value, 1 if this term is a positive real or integer value.
   */
  public int getRealOrIntegerValueSign()
  {
    return getRealOrIntegerValueSign(pointer);
  }

  private native int getRealOrIntegerValueSign(long pointer);

  /**
   * @return True if the term is an integer value.
   */
  public boolean isIntegerValue()
  {
    return isIntegerValue(pointer);
  }

  private native boolean isIntegerValue(long pointer);

  /**
   * Asserts isIntegerValue().
   * @return The integer represented by this term.
   */
  public BigInteger getIntegerValue()
  {
    return new BigInteger(getIntegerValue(pointer));
  }

  private native String getIntegerValue(long pointer);

  /**
   * @return True if the term is a string constant.
   */
  public boolean isStringValue()
  {
    return isStringValue(pointer);
  }

  private native boolean isStringValue(long pointer);

  /**
   * @return The stored string constant.
   *
   * Asserts isString().
   *
   * @api.note This method is not to be confused with {@link Term#toString()})
   *           which returns the term in some string representation, whatever
   *           data it may hold.
   */
  public String getStringValue()
  {
    return getStringValue(pointer);
  }

  private native String getStringValue(long pointer);

  /**
   * @return True if the term is a rational value.
   */
  public boolean isRealValue()
  {
    return isRealValue(pointer);
  }

  private native boolean isRealValue(long pointer);

  /**
   * Asserts isRealValue().
   * @return The representation of a rational value as a pair of its numerator.
   *         and denominator.
   */
  public Pair<BigInteger, BigInteger> getRealValue()
  {
    String rational = getRealValue(pointer);
    return Utils.getRational(rational);
  }

  private native String getRealValue(long pointer);

  /**
   * @return True if the term is a constant array.
   */
  public boolean isConstArray()
  {
    return isConstArray(pointer);
  }

  private native boolean isConstArray(long pointer);

  /**
   * Asserts isConstArray().
   * @return The base (element stored at all indices) of a constant array.
   */
  public Term getConstArrayBase()
  {
    long termPointer = getConstArrayBase(pointer);
    return new Term(termPointer);
  }

  private native long getConstArrayBase(long pointer);

  /**
   * @return True if the term is a Boolean value.
   */
  public boolean isBooleanValue()
  {
    return isBooleanValue(pointer);
  }

  private native boolean isBooleanValue(long pointer);
  /**
   * Asserts isBooleanValue().
   * @return The representation of a Boolean value as a native Boolean value.
   */
  public boolean getBooleanValue()
  {
    return getBooleanValue(pointer);
  }

  private native boolean getBooleanValue(long pointer);

  /**
   * @return True if the term is a bit-vector value.
   */
  public boolean isBitVectorValue()
  {
    return isBitVectorValue(pointer);
  }

  private native boolean isBitVectorValue(long pointer);

  /**
   * Asserts isBitVectorValue().
   * @return The representation of a bit-vector value in bit string
   *         representation.
   */
  public String getBitVectorValue() throws CVC5ApiException
  {
    return getBitVectorValue(2);
  }

  /**
   * Get the string representation of a bit-vector value.
   *
   * Supported values for {@code base} are {@code 2} (bit string), {@code 10}
   * (decimal string) or {@code 16} (hexadecimal string).
   *
   * @api.note Asserts {@code Term#isBitVectorValue()}.
   *
   * @return The string representation of a bit-vector value.
   */
  public String getBitVectorValue(int base) throws CVC5ApiException
  {
    Utils.validateUnsigned(base, "base");
    return getBitVectorValue(pointer, base);
  }

  private native String getBitVectorValue(long pointer, int base);

  /**
   * @return True if the term is a finite field value.
   */
  public boolean isFiniteFieldValue()
  {
    return isFiniteFieldValue(pointer);
  }

  private native boolean isFiniteFieldValue(long pointer);

  /**
   * Get the string representation of a finite field value.
   *
   * @api.note Asserts {@code Term#isFiniteFieldValue()}.
   *
   * @return The string representation of a finite field value.
   */
  public String getFiniteFieldValue() throws CVC5ApiException
  {
    return getFiniteFieldValue(pointer);
  }

  private native String getFiniteFieldValue(long pointer);

  /**
   * @return True if the term is an uninterpreted sort value.
   */
  public boolean isUninterpretedSortValue()
  {
    return isUninterpretedSortValue(pointer);
  }

  private native boolean isUninterpretedSortValue(long pointer);

  /**
   * Asserts isUninterpretedSortValue().
   * @return The representation of an uninterpreted sort value as a string.
   */
  public String getUninterpretedSortValue()
  {
    return getUninterpretedSortValue(pointer);
  }

  private native String getUninterpretedSortValue(long pointer);

  /**
   * @return True if the term is a floating-point rounding mode value.
   */
  public boolean isRoundingModeValue()
  {
    return isRoundingModeValue(pointer);
  }

  private native boolean isRoundingModeValue(long pointer);

  /**
   * Asserts isRoundingModeValue().
   * @return The floating-point rounding mode value held by the term.
   */
  public RoundingMode getRoundingModeValue() throws CVC5ApiException
  {
    int value = getRoundingModeValue(pointer);
    return RoundingMode.fromInt(value);
  }

  private native int getRoundingModeValue(long pointer);

  /**
   * @return True if the term is a tuple value.
   */
  public boolean isTupleValue()
  {
    return isTupleValue(pointer);
  }

  private native boolean isTupleValue(long pointer);

  /**
   * Asserts isTupleValue().
   * @return The representation of a tuple value as a vector of terms.
   */
  public Term[] getTupleValue()
  {
    long[] termPointers = getTupleValue(pointer);
    return Utils.getTerms(termPointers);
  }

  private native long[] getTupleValue(long pointer);

  /**
   * @return True if the term is the floating-point value for positive zero.
   */
  public boolean isFloatingPointPosZero()
  {
    return isFloatingPointPosZero(pointer);
  }

  private native boolean isFloatingPointPosZero(long pointer);
  /**
   * @return True if the term is the floating-point value for negative zero.
   */
  public boolean isFloatingPointNegZero()
  {
    return isFloatingPointNegZero(pointer);
  }

  private native boolean isFloatingPointNegZero(long pointer);
  /**
   * @return True if the term is the floating-point value for positive.
   * infinity.
   */
  public boolean isFloatingPointPosInf()
  {
    return isFloatingPointPosInf(pointer);
  }

  private native boolean isFloatingPointPosInf(long pointer);
  /**
   * @return True if the term is the floating-point value for negative.
   * infinity.
   */
  public boolean isFloatingPointNegInf()
  {
    return isFloatingPointNegInf(pointer);
  }

  private native boolean isFloatingPointNegInf(long pointer);
  /**
   * @return True if the term is the floating-point value for not a number.
   */
  public boolean isFloatingPointNaN()
  {
    return isFloatingPointNaN(pointer);
  }

  private native boolean isFloatingPointNaN(long pointer);
  /**
   * @return True if the term is a floating-point value.
   */
  public boolean isFloatingPointValue()
  {
    return isFloatingPointValue(pointer);
  }

  private native boolean isFloatingPointValue(long pointer);
  /**
   * Asserts isFloatingPointValue().
   * @return The representation of a floating-point value as a tuple of the.
   * exponent width, the significand width and a bit-vector value.
   */
  public Triplet<Long, Long, Term> getFloatingPointValue()
  {
    Triplet<Long, Long, Long> triplet = getFloatingPointValue(pointer);
    return new Triplet<>(triplet.first, triplet.second, new Term(triplet.third));
  }

  private native Triplet<Long, Long, Long> getFloatingPointValue(long pointer);

  /**
   * @return True if the term is a set value.
   */
  public boolean isSetValue()
  {
    return isSetValue(pointer);
  }

  private native boolean isSetValue(long pointer);
  /**
   * Asserts isSetValue().
   * @return The representation of a set value as a set of terms.
   */
  public Set<Term> getSetValue()
  {
    long[] termPointers = getSetValue(pointer);
    Term[] terms = Utils.getTerms(termPointers);
    return new HashSet<Term>(Arrays.asList(terms));
  }

  private native long[] getSetValue(long pointer);

  /**
   * @return True if the term is a sequence value.
   */
  public boolean isSequenceValue()
  {
    return isSequenceValue(pointer);
  }

  private native boolean isSequenceValue(long pointer);

  /**
   * Asserts isSequenceValue().
   * @api.note It is usually necessary for sequences to call
   *           {@link Solver#simplify(Term)} to turn a sequence that is
   *           constructed by, e.g., concatenation of unit sequences, into a
   *           sequence value.
   * @return The representation of a sequence value as a vector of terms.
   */
  public Term[] getSequenceValue()
  {
    long[] termPointers = getSequenceValue(pointer);
    return Utils.getTerms(termPointers);
  }

  private native long[] getSequenceValue(long pointer);

  /**
   * @return True if the term is a cardinality constraint.
   */
  public boolean isCardinalityConstraint()
  {
    return isCardinalityConstraint(pointer);
  }

  private native boolean isCardinalityConstraint(long pointer);

  /**
   * Asserts isCardinalityConstraint().
   * @return The sort the cardinality constraint is for and its upper bound.
   */
  public Pair<Sort, BigInteger> getCardinalityConstraint()
  {
    Pair<Long, BigInteger> pair = getCardinalityConstraint(pointer);
    Sort sort = new Sort(pair.first);
    return new Pair<Sort, BigInteger>(sort, pair.second);
  }

  private native Pair<Long, BigInteger> getCardinalityConstraint(long pointer);

  /**
   * @return True if the term is a real algebraic number.
   */
  public boolean isRealAlgebraicNumber()
  {
    return isRealAlgebraicNumber(pointer);
  }
  private native boolean isRealAlgebraicNumber(long pointer);

  /**
   * Asserts isRealAlgebraicNumber().
   * @param v The variable over which to express the polynomial.
   * @return The defining polynomial for the real algebraic number, expressed in terms of the given
   *     variable.
   */
  public Term getRealAlgebraicNumberDefiningPolynomial(Term v)
  {
    long termPointer = getRealAlgebraicNumberDefiningPolynomial(pointer, v.getPointer());
    return new Term(termPointer);
  }

  private native long getRealAlgebraicNumberDefiningPolynomial(long pointer, long termPointer);

  /**
   * Asserts isRealAlgebraicNumber().
   * @return The lower bound for the value of the real algebraic number.
   */
  public Term getRealAlgebraicNumberLowerBound()
  {
    long termPointer = getRealAlgebraicNumberLowerBound(pointer);
    return new Term(termPointer);
  }

  private native long getRealAlgebraicNumberLowerBound(long pointer);

  /**
   * Asserts isRealAlgebraicNumber().
   * @return The upper bound for the value of the real algebraic number.
   */
  public Term getRealAlgebraicNumberUpperBound()
  {
    long termPointer = getRealAlgebraicNumberUpperBound(pointer);
    return new Term(termPointer);
  }

  private native long getRealAlgebraicNumberUpperBound(long pointer);

  public class ConstIterator implements Iterator<Term>
  {
    private int currentIndex;
    private int size;

    public ConstIterator()
    {
      currentIndex = -1;
      size = getNumChildren();
    }

    @Override
    public boolean hasNext()
    {
      return currentIndex < size - 1;
    }

    @Override
    public Term next()
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

  @Override
  public Iterator<Term> iterator()
  {
    return new ConstIterator();
  }
}
