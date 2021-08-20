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

package cvc5;

import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

public class Term
    extends AbstractPointer implements Comparable<Term>, Iterable<Term> {
  // region construction and destruction
  Term(Solver solver, long pointer) {
    super(solver, pointer);
  }

  protected static native void deletePointer(long pointer);

  public long getPointer() {
    return pointer;
  }

  @Override
  public void finalize() {
    deletePointer(pointer);
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
  @Override
  public boolean equals(Object t) {
    if (this == t)
      return true;
    if (t == null || getClass() != t.getClass())
      return false;
    Term term = (Term) t;
    if (this.pointer == term.pointer) {
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
  @Override
  public int compareTo(Term t) {
    return this.compareTo(pointer, t.getPointer());
  }

  private native int compareTo(long pointer1, long pointer2);

  /**
   * @return the number of children of this term
   */
  public int getNumChildren() {
    return getNumChildren(pointer);
  }

  private native int getNumChildren(long pointer);

  /**
   * Get the child term at a given index.
   *
   * @param index the index of the child term to return
   * @return the child term with the given index
   */
  public Term getChild(int index) throws CVC5ApiException {
    Utils.validateUnsigned(index, "index");
    long termPointer = getChild(pointer, index);
    return new Term(solver, termPointer);
  }

  private native long getChild(long pointer, int index);

  /**
   * @return the id of this term
   */
  public long getId() {
    return getId(pointer);
  }

  private native long getId(long pointer);

  /**
   * @return the kind of this term
   */
  public Kind getKind() throws CVC5ApiException {
    int value = getKind(pointer);
    return Kind.fromInt(value);
  }

  private native int getKind(long pointer);

  /**
   * @return the sort of this term
   */
  public Sort getSort() {
    long sortPointer = getSort(pointer);
    return new Sort(solver, sortPointer);
  }

  private native long getSort(long pointer);

  /**
   * @return the result of replacing 'term' by 'replacement' in this term
   */
  public Term substitute(Term term, Term replacement) {
    long termPointer =
        substitute(pointer, term.getPointer(), replacement.getPointer());
    return new Term(solver, termPointer);
  }

  private native long substitute(
      long pointer, long termPointer, long replacementPointer);

  /**
   * @return the result of simultaneously replacing 'terms' by 'replacements'
   * in this term
   */
  public Term substitute(List<Term> terms, List<Term> replacements) {
    return substitute(
        terms.toArray(new Term[0]), replacements.toArray(new Term[0]));
  }

  /**
   * @return the result of simultaneously replacing 'terms' by 'replacements'
   * in this term
   */
  public Term substitute(Term[] terms, Term[] replacements) {
    long[] termPointers = new long[terms.length];
    for (int i = 0; i < termPointers.length; i++) {
      termPointers[i] = terms[i].getPointer();
    }
    long[] replacementPointers = new long[replacements.length];
    for (int i = 0; i < replacements.length; i++) {
      replacementPointers[i] = replacements[i].getPointer();
    }

    long termPointer = substitute(pointer, termPointers, replacementPointers);
    return new Term(solver, termPointer);
  }

  private native long substitute(
      long pointer, long[] termPointers, long[] replacementPointers);

  /**
   * @return true iff this term has an operator
   */
  public boolean hasOp() {
    return hasOp(pointer);
  }

  private native boolean hasOp(long pointer);

  /**
   * @return the Op used to create this term
   * Note: This is safe to call when hasOp() returns true.
   */
  public Op getOp() {
    long opPointer = getOp(pointer);
    return new Op(solver, opPointer);
  }

  private native long getOp(long pointer);

  /**
   * @return true if this Term is a null term
   */
  public boolean isNull() {
    return isNull(pointer);
  }

  private native boolean isNull(long pointer);

  /**
   * Return the base (element stored at all indices) of a constant array
   * throws an exception if the kind is not CONST_ARRAY
   *
   * @return the base value
   */
  public Term getConstArrayBase() {
    long termPointer = getConstArrayBase(pointer);
    return new Term(solver, termPointer);
  }

  private native long getConstArrayBase(long pointer);

  /**
   * Return the elements of a constant sequence
   * throws an exception if the kind is not CONST_SEQUENCE
   *
   * @return the elements of the constant sequence.
   */
  public Term[] getConstSequenceElements() {
    long[] termPointers = getConstSequenceElements(pointer);
    Term[] terms = new Term[termPointers.length];
    for (int i = 0; i < termPointers.length; i++) {
      terms[i] = new Term(solver, termPointers[i]);
    }

    return terms;
  }

  private native long[] getConstSequenceElements(long pointer);

  /**
   * Boolean negation.
   *
   * @return the Boolean negation of this term
   */
  public Term notTerm() {
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
  public Term andTerm(Term t) {
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
  public Term orTerm(Term t) {
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
  public Term xorTerm(Term t) {
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
  public Term eqTerm(Term t) {
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
  public Term impTerm(Term t) {
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
  public Term iteTerm(Term thenTerm, Term elseTerm) {
    long termPointer =
        iteTerm(pointer, thenTerm.getPointer(), elseTerm.getPointer());
    return new Term(solver, termPointer);
  }

  private native long iteTerm(long pointer, long thenPointer, long elsePointer);

  /**
   * @return a string representation of this term
   */
  protected native String toString(long pointer);

  /**
   * @return true if the term is an integer that fits within a Java integer.
   */
  public boolean isInt() {
    return isInt(pointer);
  }

  private native boolean isInt(long pointer);

  /**
   * @return the stored integer as an int.
   * Note: Asserts isInt().
   */
  public int getInt() {
    return getInt(pointer);
  }

  private native int getInt(long pointer);

  /**
   * @return true if the term is an integer that fits within a Java long.
   */
  public boolean isLong() {
    return isLong(pointer);
  }

  private native boolean isLong(long pointer);

  /**
   * @return the stored integer as a long.
   * Note: Asserts isLong().
   */
  public long getLong() {
    return getLong(pointer);
  }

  private native long getLong(long pointer);

  /**
   * @return true if the term is an integer.
   */
  public boolean isInteger() {
    return isInteger(pointer);
  }

  private native boolean isInteger(long pointer);

  /**
   * @return the stored integer in (decimal) string representation.
   * Note: Asserts isInteger().
   */
  public String getInteger() {
    return getInteger(pointer);
  }

  private native String getInteger(long pointer);

  /**
   * @return true if the term is a string constant.
   */
  public boolean isString() {
    return isString(pointer);
  }

  private native boolean isString(long pointer);

  /**
   * @return the stored string constant.
   * <p>
   * Note: This method is not to be confused with toString() which returns the
   * term in some string representation, whatever data it may hold.
   * Asserts isString().
   */
  public String getString() {
    return getString(pointer);
  }

  private native String getString(long pointer);

  public class ConstIterator implements Iterator<Term> {
    private int currentIndex;
    private int size;

    public ConstIterator() {
      currentIndex = -1;
      size = getNumChildren();
    }

    @Override
    public boolean hasNext() {
      return currentIndex < size - 1;
    }

    @Override
    public Term next() {
      if (currentIndex >= size - 1) {
        throw new NoSuchElementException();
      }
      currentIndex++;
      try {
        return getChild(currentIndex);
      } catch (CVC5ApiException e) {
        e.printStackTrace();
        throw new RuntimeException(e.getMessage());
      }
    }
  }

  @Override
  public Iterator<Term> iterator() {
    return new ConstIterator();
  }
}
