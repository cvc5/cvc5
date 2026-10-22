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

import static java.lang.foreign.ValueLayout.ADDRESS;
import static java.lang.foreign.ValueLayout.JAVA_INT;
import static java.lang.foreign.ValueLayout.JAVA_LONG;

import io.github.cvc5.capi.CApi;
import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.BinaryOperator;

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
    super(null, MemorySegment.NULL, null);
  }

  Term(NativeContext ctx, MemorySegment pointer)
  {
    super(ctx, pointer, Term::deletePointer);
  }

  private static void deletePointer(MemorySegment pointer)
  {
    CApi.cvc5_term_release(pointer);
  }

  /**
   * Syntactic equality operator.
   * Return true if both terms are syntactically identical.
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
    if (this.address() == term.address())
    {
      return true;
    }
    return equals(handle(), term.handle());
  }

  private boolean equals(MemorySegment pointer1, MemorySegment pointer2)
  {
    return Native.check(CApi.cvc5_term_is_equal(pointer1, pointer2));
  }

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
    return this.compareTo(handle(), t.handle());
  }

  private int compareTo(MemorySegment pointer1, MemorySegment pointer2)
  {
    if (pointer1.address() == 0 || pointer2.address() == 0)
    {
      // The C API rejects null terms. Terms are ordered by their ids, and a null
      // term has the smallest id.
      return pointer1.address() == pointer2.address() ? 0 : (pointer1.address() == 0 ? -1 : 1);
    }
    return (int) Native.check(CApi.cvc5_term_compare(pointer1, pointer2));
  }

  /**
   * Get the number of children of this term.
   *
   * @return The number of children of this term.
   */
  public int getNumChildren()
  {
    return getNumChildren(handle());
  }

  private int getNumChildren(MemorySegment pointer)
  {
    return (int) Native.check(CApi.cvc5_term_get_num_children(pointer));
  }

  /**
   * Get the child term at a given index.
   *
   * @param index The index of the child term to return.
   * @return The child term with the given index.
   * @throws CVC5ApiException on error
   */
  public Term getChild(int index) throws CVC5ApiException
  {
    Utils.validateUnsigned(index, "index");
    MemorySegment termPointer = getChild(handle(), index);
    return new Term(ctx, termPointer);
  }

  private MemorySegment getChild(MemorySegment pointer, int index)
  {
    return Native.handle(CApi.cvc5_term_get_child(pointer, index));
  }

  /**
   * Get the id of this term.
   *
   * @return The id of this term.
   */
  public long getId()
  {
    return getId(handle());
  }

  private long getId(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_get_id(pointer));
  }

  /**
   * Get the kind of this term.
   *
   * @return The kind of this term.
   * @throws CVC5ApiException on error
   */
  public Kind getKind() throws CVC5ApiException
  {
    int value = getKind(handle());
    return Kind.fromInt(value);
  }

  private int getKind(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_get_kind(pointer));
  }

  /**
   * Get the sort of this term.
   *
   * @return The sort of this term.
   */
  public Sort getSort()
  {
    MemorySegment sortPointer = getSort(handle());
    return new Sort(ctx, sortPointer);
  }

  private MemorySegment getSort(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_term_get_sort(pointer));
  }

  /**
   * Replace {@code term} with {@code replacement} in this term.
   *
   * @param term        The term to replace.
   * @param replacement The term to replace it with.
   * @return The result of replacing {@code term} with {@code replacement} in
   *         this term.
   *
   * @api.note This replacement is applied during a pre-order traversal and
   *           only once (it is not run until fixed point).
   */
  public Term substitute(Term term, Term replacement)
  {
    MemorySegment termPointer = substitute(handle(), term.handle(), replacement.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment substitute(
      MemorySegment pointer, MemorySegment termPointer, MemorySegment replacementPointer)
  {
    return Native.handle(CApi.cvc5_term_substitute_term(pointer, termPointer, replacementPointer));
  }

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
   * @param terms        The terms to replace.
   * @param replacements The replacement terms.
   * @return The result of simultaneously replacing {@code terms} with
   *         {@code replacements} in this term.
   */
  public Term substitute(Term[] terms, Term[] replacements)
  {
    MemorySegment[] termPointers = new MemorySegment[terms.length];
    for (int i = 0; i < termPointers.length; i++)
    {
      termPointers[i] = terms[i].handle();
    }
    MemorySegment[] replacementPointers = new MemorySegment[replacements.length];
    for (int i = 0; i < replacements.length; i++)
    {
      replacementPointers[i] = replacements[i].handle();
    }

    MemorySegment termPointer = substitute(handle(), termPointers, replacementPointers);
    return new Term(ctx, termPointer);
  }

  private MemorySegment substitute(
      MemorySegment pointer, MemorySegment[] termPointers, MemorySegment[] replacementPointers)
  {
    // The C API takes a single size for both arrays.
    if (termPointers.length != replacementPointers.length)
    {
      throw new CVC5ApiException("expected vectors of the same arity in substitute");
    }
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_term_substitute_terms(pointer,
          termPointers.length,
          Native.allocateHandles(arena, termPointers),
          Native.allocateHandles(arena, replacementPointers)));
    }
  }

  /**
   * Determine if this term has an operator.
   *
   * @return True iff this term has an operator.
   */
  public boolean hasOp()
  {
    return hasOp(handle());
  }

  private boolean hasOp(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_has_op(pointer));
  }

  /**
   * Get the Op used to create this term.
   *
   * @return The Op used to create this term.
   * @api.note This is safe to call when {@link Term#hasOp()} returns true.
   */
  public Op getOp()
  {
    MemorySegment opPointer = getOp(handle());
    return new Op(ctx, opPointer);
  }

  private MemorySegment getOp(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_term_get_op(pointer));
  }

  /**
   * Determine if the term has a symbol.
   *
   * @return True if the term has a symbol.
   */
  public boolean hasSymbol()
  {
    return hasSymbol(handle());
  }

  private boolean hasSymbol(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_has_symbol(pointer));
  }

  /**
   * Asserts hasSymbol().
   * @return The raw symbol of the term.
   */
  public String getSymbol()
  {
    return getSymbol(handle());
  }

  private String getSymbol(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_term_get_symbol(pointer));
  }

  /**
   * Determine if this term is a null term.
   *
   * @return True if this Term is a null term.
   */
  public boolean isNull()
  {
    return isNull(handle());
  }

  private boolean isNull(MemorySegment pointer)
  {
    return pointer.address() == 0;
  }

  /**
   * Boolean negation.
   *
   * @return The Boolean negation of this term.
   */
  public Term notTerm()
  {
    MemorySegment termPointer = notTerm(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment notTerm(MemorySegment pointer)
  {
    return mkTerm(Kind.NOT, pointer);
  }

  /**
   * Boolean and.
   *
   * @param t A Boolean term.
   * @return The conjunction of this term and the given term.
   */
  public Term andTerm(Term t)
  {
    MemorySegment termPointer = andTerm(handle(), t.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment andTerm(MemorySegment pointer, MemorySegment termPointer)
  {
    return mkTerm(Kind.AND, pointer, termPointer);
  }

  /**
   * Boolean or.
   *
   * @param t A Boolean term.
   * @return The disjunction of this term and the given term.
   */
  public Term orTerm(Term t)
  {
    MemorySegment termPointer = orTerm(handle(), t.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment orTerm(MemorySegment pointer, MemorySegment termPointer)
  {
    return mkTerm(Kind.OR, pointer, termPointer);
  }

  /**
   * Boolean exclusive or.
   *
   * @param t A Boolean term.
   * @return The exclusive disjunction of this term and the given term.
   */
  public Term xorTerm(Term t)
  {
    MemorySegment termPointer = xorTerm(handle(), t.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment xorTerm(MemorySegment pointer, MemorySegment termPointer)
  {
    return mkTerm(Kind.XOR, pointer, termPointer);
  }

  /**
   * Equality.
   *
   * @param t A Boolean term.
   * @return The Boolean equivalence of this term and the given term.
   */
  public Term eqTerm(Term t)
  {
    MemorySegment termPointer = eqTerm(handle(), t.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment eqTerm(MemorySegment pointer, MemorySegment termPointer)
  {
    return mkTerm(Kind.EQUAL, pointer, termPointer);
  }

  /**
   * Boolean implication.
   *
   * @param t A Boolean term.
   * @return The implication of this term and the given term.
   */
  public Term impTerm(Term t)
  {
    MemorySegment termPointer = impTerm(handle(), t.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment impTerm(MemorySegment pointer, MemorySegment termPointer)
  {
    return mkTerm(Kind.IMPLIES, pointer, termPointer);
  }

  /**
   * If-then-else with this term as the Boolean condition.
   *
   * @param thenTerm The 'then' term.
   * @param elseTerm The 'else' term.
   * @return The if-then-else term with this term as the Boolean condition.
   */
  public Term iteTerm(Term thenTerm, Term elseTerm)
  {
    MemorySegment termPointer = iteTerm(handle(), thenTerm.handle(), elseTerm.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment iteTerm(
      MemorySegment pointer, MemorySegment thenPointer, MemorySegment elsePointer)
  {
    return mkTerm(Kind.ITE, pointer, thenPointer, elsePointer);
  }

  /**
   * Create a term of the given kind with the given children, the first of
   * which is this term, via the term manager of this term (the C API has no
   * counterparts of {@code Term::notTerm()} etc.).
   *
   * @param kind The kind of the term.
   * @param children The children of the term.
   * @return The pointer of the new term.
   */
  private MemorySegment mkTerm(Kind kind, MemorySegment... children)
  {
    if (ctx == null)
    {
      // This is a null term, which has no term manager.
      throw new CVC5ApiException("invalid term");
    }
    try (Arena arena = Arena.ofConfined())
    {
      return Native.handle(CApi.cvc5_mk_term(
          ctx.tm, kind.getValue(), children.length, Native.allocateHandles(arena, children)));
    }
  }

  /**
   * @return A string representation of this term.
   */
  protected String toString(long pointer)
  {
    if (pointer == 0)
    {
      return "null";
    }
    return Native.string(CApi.cvc5_term_to_string(MemorySegment.ofAddress(pointer)));
  }

  /**
   * Get integer or real value sign. Must be called on integer or real values,
   * or otherwise an exception is thrown.
   * @return 0 if this term is zero, -1 if this term is a negative real or
   *         integer value, 1 if this term is a positive real or integer value.
   */
  public int getRealOrIntegerValueSign()
  {
    return getRealOrIntegerValueSign(handle());
  }

  private int getRealOrIntegerValueSign(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_get_real_or_integer_value_sign(pointer));
  }

  /**
   * Determine if the term is an integer value.
   *
   * @return True if the term is an integer value.
   */
  public boolean isIntegerValue()
  {
    return isIntegerValue(handle());
  }

  private boolean isIntegerValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_integer_value(pointer));
  }

  /**
   * Asserts isIntegerValue().
   * @return The integer represented by this term.
   */
  public BigInteger getIntegerValue()
  {
    return new BigInteger(getIntegerValue(handle()));
  }

  private String getIntegerValue(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_term_get_integer_value(pointer));
  }

  /**
   * Determine if the term is a string constant.
   *
   * @return True if the term is a string constant.
   */
  public boolean isStringValue()
  {
    return isStringValue(handle());
  }

  private boolean isStringValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_string_value(pointer));
  }

  /**
   * Get the stored string constant.
   *
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
    return getStringValue(handle());
  }

  private String getStringValue(MemorySegment pointer)
  {
    return Native.u32string(CApi.cvc5_term_get_u32string_value(pointer));
  }

  /**
   * Determine if the term is a rational value.
   *
   * @return True if the term is a rational value.
   */
  public boolean isRealValue()
  {
    return isRealValue(handle());
  }

  private boolean isRealValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_real_value(pointer));
  }

  /**
   * Asserts isRealValue().
   * @return The representation of a rational value as a pair of its numerator.
   *         and denominator.
   */
  public Pair<BigInteger, BigInteger> getRealValue()
  {
    String rational = getRealValue(handle());
    return Utils.getRational(rational);
  }

  private String getRealValue(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_term_get_real_value(pointer));
  }

  /**
   * Determine if the term is a constant array.
   *
   * @return True if the term is a constant array.
   */
  public boolean isConstArray()
  {
    return isConstArray(handle());
  }

  private boolean isConstArray(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_const_array(pointer));
  }

  /**
   * Asserts isConstArray().
   * @return The base (element stored at all indices) of a constant array.
   */
  public Term getConstArrayBase()
  {
    MemorySegment termPointer = getConstArrayBase(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getConstArrayBase(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_term_get_const_array_base(pointer));
  }

  /**
   * Determine if the term is a Boolean value.
   *
   * @return True if the term is a Boolean value.
   */
  public boolean isBooleanValue()
  {
    return isBooleanValue(handle());
  }

  private boolean isBooleanValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_boolean_value(pointer));
  }
  /**
   * Asserts isBooleanValue().
   * @return The representation of a Boolean value as a native Boolean value.
   */
  public boolean getBooleanValue()
  {
    return getBooleanValue(handle());
  }

  private boolean getBooleanValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_get_boolean_value(pointer));
  }

  /**
   * Determine if the term is a bit-vector value.
   *
   * @return True if the term is a bit-vector value.
   */
  public boolean isBitVectorValue()
  {
    return isBitVectorValue(handle());
  }

  private boolean isBitVectorValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_bv_value(pointer));
  }

  /**
   * Asserts isBitVectorValue().
   * @return The representation of a bit-vector value in bit string
   *         representation.
   * @throws CVC5ApiException on error
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
   * @param base {@code 2} for binary, {@code 10} for decimal, and {@code 16}
   *             for hexadecimal.
   * @return The string representation of a bit-vector value.
   * @throws CVC5ApiException on error
   */
  public String getBitVectorValue(int base) throws CVC5ApiException
  {
    Utils.validateUnsigned(base, "base");
    return getBitVectorValue(handle(), base);
  }

  private String getBitVectorValue(MemorySegment pointer, int base)
  {
    return Native.string(CApi.cvc5_term_get_bv_value(pointer, base));
  }

  /**
   * Determine if the term is a finite field value.
   *
   * @return True if the term is a finite field value.
   */
  public boolean isFiniteFieldValue()
  {
    return isFiniteFieldValue(handle());
  }

  private boolean isFiniteFieldValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_ff_value(pointer));
  }

  /**
   * Get the string representation of a finite field value.
   *
   * @api.note Asserts {@code Term#isFiniteFieldValue()}.
   *
   * @return The string representation of a finite field value.
   * @throws CVC5ApiException on error
   */
  public String getFiniteFieldValue() throws CVC5ApiException
  {
    return getFiniteFieldValue(handle());
  }

  private String getFiniteFieldValue(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_term_get_ff_value(pointer));
  }

  /**
   * Determine if the term is an uninterpreted sort value.
   *
   * @return True if the term is an uninterpreted sort value.
   */
  public boolean isUninterpretedSortValue()
  {
    return isUninterpretedSortValue(handle());
  }

  private boolean isUninterpretedSortValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_uninterpreted_sort_value(pointer));
  }

  /**
   * Asserts isUninterpretedSortValue().
   * @return The representation of an uninterpreted sort value as a string.
   */
  public String getUninterpretedSortValue()
  {
    return getUninterpretedSortValue(handle());
  }

  private String getUninterpretedSortValue(MemorySegment pointer)
  {
    return Native.string(CApi.cvc5_term_get_uninterpreted_sort_value(pointer));
  }

  /**
   * Determine if the term is a floating-point rounding mode value.
   *
   * @return True if the term is a floating-point rounding mode value.
   */
  public boolean isRoundingModeValue()
  {
    return isRoundingModeValue(handle());
  }

  private boolean isRoundingModeValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_rm_value(pointer));
  }

  /**
   * Asserts isRoundingModeValue().
   * @return The floating-point rounding mode value held by the term.
   * @throws CVC5ApiException on error
   */
  public RoundingMode getRoundingModeValue() throws CVC5ApiException
  {
    int value = getRoundingModeValue(handle());
    return RoundingMode.fromInt(value);
  }

  private int getRoundingModeValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_get_rm_value(pointer));
  }

  /**
   * Determine if the term is a tuple value.
   *
   * @return True if the term is a tuple value.
   */
  public boolean isTupleValue()
  {
    return isTupleValue(handle());
  }

  private boolean isTupleValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_tuple_value(pointer));
  }

  /**
   * Asserts isTupleValue().
   * @return The representation of a tuple value as a vector of terms.
   */
  public Term[] getTupleValue()
  {
    MemorySegment[] termPointers = getTupleValue(handle());
    return Utils.getTerms(ctx, termPointers);
  }

  private MemorySegment[] getTupleValue(MemorySegment pointer)
  {
    return getTerms(pointer, CApi::cvc5_term_get_tuple_value);
  }

  /**
   * Get an array of terms from a C API function that returns the array and
   * writes its size to an out-parameter.
   *
   * @param pointer The pointer of the term to query.
   * @param getter The C API function, taking the term and the address of the
   *               size.
   * @return The pointers of the terms, each of which is owned by the caller.
   */
  private static MemorySegment[] getTerms(
      MemorySegment pointer, BinaryOperator<MemorySegment> getter)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment size = arena.allocate(JAVA_LONG);
      MemorySegment terms = Native.check(getter.apply(pointer, size));
      return Native.handles(terms, size.get(JAVA_LONG, 0));
    }
  }

  /**
   * Determine if the term is the floating-point value for positive zero.
   *
   * @return True if the term is the floating-point value for positive zero.
   */
  public boolean isFloatingPointPosZero()
  {
    return isFloatingPointPosZero(handle());
  }

  private boolean isFloatingPointPosZero(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_fp_pos_zero(pointer));
  }

  /**
   * Determine if the term is the floating-point value for negative zero.
   *
   * @return True if the term is the floating-point value for negative zero.
   */
  public boolean isFloatingPointNegZero()
  {
    return isFloatingPointNegZero(handle());
  }

  private boolean isFloatingPointNegZero(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_fp_neg_zero(pointer));
  }
  /**
   * Determine if the term is the floating-point value for positive.
   *
   * @return True if the term is the floating-point value for positive.
   * infinity.
   */
  public boolean isFloatingPointPosInf()
  {
    return isFloatingPointPosInf(handle());
  }

  private boolean isFloatingPointPosInf(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_fp_pos_inf(pointer));
  }

  /**
   * Determine if the term is the floating-point value for negative.
   * infinity.
   *
   * @return True if the term is the floating-point value for negative.
   * infinity.
   */
  public boolean isFloatingPointNegInf()
  {
    return isFloatingPointNegInf(handle());
  }

  private boolean isFloatingPointNegInf(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_fp_neg_inf(pointer));
  }
  /**
   * Determine if the term is the floating-point value for not a number.
   *
   * @return True if the term is the floating-point value for not a number.
   */
  public boolean isFloatingPointNaN()
  {
    return isFloatingPointNaN(handle());
  }

  private boolean isFloatingPointNaN(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_fp_nan(pointer));
  }
  /**
   * Determine if the term is a floating-point value.
   *
   * @return True if the term is a floating-point value.
   */
  public boolean isFloatingPointValue()
  {
    return isFloatingPointValue(handle());
  }

  private boolean isFloatingPointValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_fp_value(pointer));
  }
  /**
   * Asserts isFloatingPointValue().
   * @return The representation of a floating-point value as a tuple of the.
   * exponent width, the significand width and a bit-vector value.
   */
  public Triplet<Long, Long, Term> getFloatingPointValue()
  {
    Triplet<String, String, MemorySegment> triplet = getFloatingPointValue(handle());
    Long exponent = Long.valueOf(triplet.first);
    Long significand = Long.valueOf(triplet.second);
    return new Triplet<>(exponent, significand, new Term(ctx, triplet.third));
  }

  private Triplet<String, String, MemorySegment> getFloatingPointValue(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment ew = arena.allocate(JAVA_INT);
      MemorySegment sw = arena.allocate(JAVA_INT);
      MemorySegment val = arena.allocate(ADDRESS);
      CApi.cvc5_term_get_fp_value(pointer, ew, sw, val);
      Native.check();
      return new Triplet<>(Integer.toUnsignedString(ew.get(JAVA_INT, 0)),
          Integer.toUnsignedString(sw.get(JAVA_INT, 0)),
          val.get(ADDRESS, 0));
    }
  }

  /**
   * Determine if the term is a set value.
   *
   * @return True if the term is a set value.
   */
  public boolean isSetValue()
  {
    return isSetValue(handle());
  }

  private boolean isSetValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_set_value(pointer));
  }
  /**
   * Asserts isSetValue().
   * @return The representation of a set value as a set of terms.
   */
  public Set<Term> getSetValue()
  {
    MemorySegment[] termPointers = getSetValue(handle());
    Term[] terms = Utils.getTerms(ctx, termPointers);
    return new HashSet<Term>(Arrays.asList(terms));
  }

  private MemorySegment[] getSetValue(MemorySegment pointer)
  {
    return getTerms(pointer, CApi::cvc5_term_get_set_value);
  }

  /**
   * Determine if the term is a sequence value.
   *
   * @return True if the term is a sequence value.
   */
  public boolean isSequenceValue()
  {
    return isSequenceValue(handle());
  }

  private boolean isSequenceValue(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_sequence_value(pointer));
  }

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
    MemorySegment[] termPointers = getSequenceValue(handle());
    return Utils.getTerms(ctx, termPointers);
  }

  private MemorySegment[] getSequenceValue(MemorySegment pointer)
  {
    return getTerms(pointer, CApi::cvc5_term_get_sequence_value);
  }

  /**
   * Determine if the term is a cardinality constraint.
   *
   * @return True if the term is a cardinality constraint.
   */
  public boolean isCardinalityConstraint()
  {
    return isCardinalityConstraint(handle());
  }

  private boolean isCardinalityConstraint(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_cardinality_constraint(pointer));
  }

  /**
   * Asserts isCardinalityConstraint().
   * @return The sort the cardinality constraint is for and its upper bound.
   */
  public Pair<Sort, BigInteger> getCardinalityConstraint()
  {
    Pair<MemorySegment, BigInteger> pair = getCardinalityConstraint(handle());
    Sort sort = new Sort(ctx, pair.first);
    return new Pair<Sort, BigInteger>(sort, pair.second);
  }

  private Pair<MemorySegment, BigInteger> getCardinalityConstraint(MemorySegment pointer)
  {
    try (Arena arena = Arena.ofConfined())
    {
      MemorySegment sort = arena.allocate(ADDRESS);
      MemorySegment upper = arena.allocate(JAVA_INT);
      CApi.cvc5_term_get_cardinality_constraint(pointer, sort, upper);
      Native.check();
      return new Pair<>(
          sort.get(ADDRESS, 0), BigInteger.valueOf(Integer.toUnsignedLong(upper.get(JAVA_INT, 0))));
    }
  }

  /**
   * Determine if the term is a real algebraic number.
   *
   * @return True if the term is a real algebraic number.
   */
  public boolean isRealAlgebraicNumber()
  {
    return isRealAlgebraicNumber(handle());
  }
  private boolean isRealAlgebraicNumber(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_real_algebraic_number(pointer));
  }

  /**
   * Asserts isRealAlgebraicNumber().
   * @param v The variable over which to express the polynomial.
   * @return The defining polynomial for the real algebraic number, expressed in terms of the given
   *     variable.
   */
  public Term getRealAlgebraicNumberDefiningPolynomial(Term v)
  {
    MemorySegment termPointer = getRealAlgebraicNumberDefiningPolynomial(handle(), v.handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getRealAlgebraicNumberDefiningPolynomial(
      MemorySegment pointer, MemorySegment termPointer)
  {
    return Native.handle(
        CApi.cvc5_term_get_real_algebraic_number_defining_polynomial(pointer, termPointer));
  }

  /**
   * Asserts isRealAlgebraicNumber().
   * @return The lower bound for the value of the real algebraic number.
   */
  public Term getRealAlgebraicNumberLowerBound()
  {
    MemorySegment termPointer = getRealAlgebraicNumberLowerBound(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getRealAlgebraicNumberLowerBound(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_term_get_real_algebraic_number_lower_bound(pointer));
  }

  /**
   * Asserts isRealAlgebraicNumber().
   * @return The upper bound for the value of the real algebraic number.
   */
  public Term getRealAlgebraicNumberUpperBound()
  {
    MemorySegment termPointer = getRealAlgebraicNumberUpperBound(handle());
    return new Term(ctx, termPointer);
  }

  private MemorySegment getRealAlgebraicNumberUpperBound(MemorySegment pointer)
  {
    return Native.handle(CApi.cvc5_term_get_real_algebraic_number_upper_bound(pointer));
  }

  /**
   * Determine if this term is a skolem function.
   *
   * @api.note This method is experimental and may change in future versions.
   * @return True if this term is a skolem function.
   */
  public boolean isSkolem()
  {
    return isSkolem(handle());
  }
  private boolean isSkolem(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_is_skolem(pointer));
  }

  /**
   * Get skolem identifier of this term.
   * @api.note Asserts isSkolem().
   * @api.note This method is experimental and may change in future versions.
   * @return The skolem identifier of this term.
   * @throws CVC5ApiException on error
   */
  public SkolemId getSkolemId() throws CVC5ApiException
  {
    int value = getSkolemId(handle());
    return SkolemId.fromInt(value);
  }

  private int getSkolemId(MemorySegment pointer)
  {
    return Native.check(CApi.cvc5_term_get_skolem_id(pointer));
  }

  /**
   * Get the skolem indices of this term.
   * @api.note Asserts isSkolem().
   * @api.note This method is experimental and may change in future versions.
   * @return The skolem indices of this term. This a list of terms that the
   * skolem function is indexed by. For example, the array diff skolem
   * {@link SkolemId#ARRAY_DEQ_DIFF} is indexed by two arrays.
   * @throws CVC5ApiException on error
   */
  public Term[] getSkolemIndices() throws CVC5ApiException
  {
    MemorySegment[] termPointers = getSkolemIndices(handle());
    return Utils.getTerms(ctx, termPointers);
  }

  private MemorySegment[] getSkolemIndices(MemorySegment pointer)
  {
    return getTerms(pointer, CApi::cvc5_term_get_skolem_indices);
  }

  /**
   * ConstIterator is an implementation of the {@link Iterator} interface for iterating over
   * a collection of {@code Term} objects. It provides read-only access to the elements.
   */
  public class ConstIterator implements Iterator<Term>
  {
    private int currentIndex;
    private int size;

    /**
     * Constructs a new ConstIterator.
     */
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

  /**
   * Get the hash value of a term.
   * @return The hash value.
   */
  @Override
  public int hashCode()
  {
    return Long.hashCode(hashCode(handle()));
  }

  private long hashCode(MemorySegment pointer)
  {
    if (pointer.address() == 0)
    {
      // The C API rejects null terms. The hash value of a term is its id, which
      // is 0 for null terms.
      return 0;
    }
    return Native.check(CApi.cvc5_term_hash(pointer));
  }
}
