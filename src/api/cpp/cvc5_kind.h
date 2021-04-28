/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Makai Mann
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The term kinds of the cvc5 C++ API.
 */

#include "cvc5_export.h"

#ifndef CVC5__API__CVC5_KIND_H
#define CVC5__API__CVC5_KIND_H

#include <ostream>

namespace cvc5 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

// TODO(Gereon): Fix links that involve std::vector. See https://github.com/doxygen/doxygen/issues/8503
/**
 * The kind of a cvc5 term.
 *
 * Note that the underlying type of Kind must be signed (to enable range
 * checks for validity). The size of this type depends on the size of
 * cvc5::Kind (NodeValue::NBITS_KIND, currently 10 bits, see expr/node_value.h).
 */
enum CVC5_EXPORT Kind : int32_t
{
  /**
   * Internal kind.
   * Should never be exposed or created via the API.
   */
  INTERNAL_KIND = -2,
  /**
   * Undefined kind.
   * Should never be exposed or created via the API.
   */
  UNDEFINED_KIND = -1,
  /**
   * Null kind (kind of null term `Term::Term()`).
   * Do not explicitly create via API functions other than `Term::Term()`.
   */
  NULL_EXPR,

  /* Builtin --------------------------------------------------------------- */

  /**
   * Uninterpreted constant.
   *
   * Parameters:
   *   - 1: Sort of the constant
   *   - 2: Index of the constant
   *
   * Create with:
   *   - `Solver::mkUninterpretedConst(const Sort& sort, int32_t index) const`
   */
  UNINTERPRETED_CONSTANT,
  /**
   * Abstract value (other than uninterpreted sort constants).
   *
   * Parameters:
   *   - 1: Index of the abstract value
   *
   * Create with:
   *   - `Solver::mkAbstractValue(const std::string& index) const`
   *   - `Solver::mkAbstractValue(uint64_t index) const`
   */
  ABSTRACT_VALUE,
#if 0
  /* Built-in operator */
  BUILTIN,
#endif
  /**
   * Equality, chainable.
   *
   * Parameters: n > 1
   *   - 1..n: Terms with same sorts
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  EQUAL,
  /**
   * Disequality.
   *
   * Parameters: n > 1
   *   - 1..n: Terms with same sorts
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  DISTINCT,
  /**
   * First-order constant.
   *
   * Not permitted in bindings (forall, exists, ...).
   *
   * Parameters:
   *   - See @ref cvc5::api::Solver::mkConst() "mkConst()".
   *
   * Create with:
   *   - `Solver::mkConst(const Sort& sort, const std::string& symbol) const`
   *   - `Solver::mkConst(const Sort& sort) const`
   */
  CONSTANT,
  /**
   * (Bound) variable.
   *
   * Permitted in bindings and in the lambda and quantifier bodies only.
   *
   * Parameters:
   *   - See @ref cvc5::api::Solver::mkVar() "mkVar()".
   *
   * Create with:
   *   - `Solver::mkVar(const Sort& sort, const std::string& symbol) const`
   */
  VARIABLE,
#if 0
  /* Skolem variable (internal only) */
  SKOLEM,
#endif
  /**
   * Symbolic expression.
   *
   * Parameters: n > 0
   *   - 1..n: terms
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEXPR,
  /**
   * Lambda expression.
   *
   * Parameters:
   *   - 1: BOUND_VAR_LIST
   *   - 2: Lambda body
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  LAMBDA,
  /**
   * The syntax of a witness term is similar to a quantified formula except that
   * only one bound variable is allowed.
   * The term `(witness ((x T)) F)` returns an element `x` of type `T`
   * and asserts `F`.
   *
   * The witness operator behaves like the description operator
   * (see https://planetmath.org/hilbertsvarepsilonoperator) if there is no x
   * that satisfies F. But if such x exists, the witness operator does not
   * enforce the axiom that ensures uniqueness up to logical equivalence:
   *
   * @f[
   *   \forall x. F \equiv G \Rightarrow witness~x. F =  witness~x. G
   * @f]
   *
   * For example if there are 2 elements of type T that satisfy F, then the
   * following formula is satisfiable:
   *
   *     (distinct
   *        (witness ((x Int)) F)
   *        (witness ((x Int)) F))
   *
   * This kind is primarily used internally, but may be returned in models
   * (e.g. for arithmetic terms in non-linear queries). However, it is not
   * supported by the parser. Moreover, the user of the API should be cautious
   * when using this operator. In general, all witness terms
   * `(witness ((x Int)) F)` should be such that `(exists ((x Int)) F)` is a
   * valid formula. If this is not the case, then the semantics in formulas that
   * use witness terms may be unintuitive. For example, the following formula is
   * unsatisfiable:
   * `(or (= (witness ((x Int)) false) 0) (not (= (witness ((x Int)) false) 0))`
   * whereas notice that `(or (= z 0) (not (= z 0)))` is true for any `z`.
   *
   * Parameters:
   *   - 1: BOUND_VAR_LIST
   *   - 2: Witness body
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  WITNESS,

  /* Boolean --------------------------------------------------------------- */

  /**
   * Boolean constant.
   *
   * Parameters:
   *   - 1: Boolean value of the constant
   *
   * Create with:
   *   - `Solver::mkTrue() const`
   *   - `Solver::mkFalse() const`
   *   - `Solver::mkBoolean(bool val) const`
   */
  CONST_BOOLEAN,
  /**
   * Logical negation.
   *
   * Parameters:
   *   - 1: Boolean Term to negate
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  NOT,
  /**
   * Logical conjunction.
   *
   * Parameters: n > 1
   *   - 1..n: Boolean Term of the conjunction
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  AND,
  /**
   * Logical implication.
   *
   * Parameters: n > 1
   *   - 1..n: Boolean Terms, right associative
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  IMPLIES,
  /**
   * Logical disjunction.
   *
   * Parameters: n > 1
   *   - 1..n: Boolean Term of the disjunction
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  OR,
  /**
   * Logical exclusive disjunction, left associative.
   *
   * Parameters: n > 1
   *   - 1..n: Boolean Terms, `[1] xor ... xor [n]`
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  XOR,
  /**
   * If-then-else.
   *
   * Parameters:
   *   - 1: is a Boolean condition Term
   *   - 2: the 'then' Term
   *   - 3: the 'else' Term
   *
   * 'then' and 'else' term must have same base sort.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  ITE,

  /* UF -------------------------------------------------------------------- */

  /**
   * Application of an uninterpreted function.
   *
   * Parameters: n > 1
   *   - 1: Function Term
   *   - 2..n: Function argument instantiation Terms
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  APPLY_UF,
#if 0
  /* Boolean term variable */
  BOOLEAN_TERM_VARIABLE,
#endif
  /**
   * Cardinality constraint on uninterpreted sort S.
   * Interpreted as a predicate that is true when the cardinality of S
   * is less than or equal to the value of the second argument.
   *
   * Parameters:
   *   - 1: Term of sort S
   *   - 2: Positive integer constant that bounds the cardinality of sort S
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  CARDINALITY_CONSTRAINT,
  /**
   * Cardinality value for uninterpreted sort S.
   * An operator that returns an integer indicating the value of the cardinality
   * of sort S.
   *
   * Parameters:
   *   - 1: Term of sort S
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  CARDINALITY_VALUE,
#if 0
  /* Combined cardinality constraint.  */
  COMBINED_CARDINALITY_CONSTRAINT,
  /* Partial uninterpreted function application.  */
  PARTIAL_APPLY_UF,
#endif
  /**
   * Higher-order applicative encoding of function application, left
   * associative.
   *
   * Parameters: n > 1
   *   - 1: Function to apply
   *   - 2..n: Arguments of the function
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  HO_APPLY,

  /* Arithmetic ------------------------------------------------------------ */

  /**
   * Arithmetic addition.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer, Real (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  PLUS,
  /**
   * Arithmetic multiplication.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer, Real (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  MULT,
  /**
   * Operator for Integer AND
   *
   * Parameters:
   *   - 1: Size of the bit-vector that determines the semantics of the IAND
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`
   *
   * Apply integer conversion to bit-vector.

   * Parameters:
   *   - 1: Op of kind IAND
   *   - 2: Integer term
   *   - 3: Integer term
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  IAND,
#if 0
  /* Synonym for MULT.  */
  NONLINEAR_MULT,
#endif
  /**
   * Arithmetic subtraction, left associative.
   *
   * Parameters:
   *   - 1..n: Terms of sort Integer, Real (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  MINUS,
  /**
   * Arithmetic negation.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  UMINUS,
  /**
   * Real division, division by 0 undefined, left associative.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  DIVISION,
  /**
   * Integer division, division by 0 undefined, left associative.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INTS_DIVISION,
  /**
   * Integer modulus, division by 0 undefined.
   *
   * Parameters:
   *   - 1: Term of sort Integer
   *   - 2: Term of sort Integer
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INTS_MODULUS,
  /**
   * Absolute value.
   *
   * Parameters:
   *   - 1: Term of sort Integer
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ABS,
  /**
   * Arithmetic power.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *   - 2: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  POW,
  /**
   * Exponential function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  EXPONENTIAL,
  /**
   * Sine function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  SINE,
  /**
   * Cosine function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  COSINE,
  /**
   * Tangent function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  TANGENT,
  /**
   * Cosecant function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  COSECANT,
  /**
   * Secant function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  SECANT,
  /**
   * Cotangent function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  COTANGENT,
  /**
   * Arc sine function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ARCSINE,
  /**
   * Arc cosine function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ARCCOSINE,
  /**
   * Arc tangent function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ARCTANGENT,
  /**
   * Arc cosecant function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ARCCOSECANT,
  /**
   * Arc secant function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ARCSECANT,
  /**
   * Arc cotangent function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  ARCCOTANGENT,
  /**
   * Square root.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  SQRT,
  /**
   * Operator for the divisibility-by-k predicate.
   *
   * Parameter:
   *   - 1: The k to divide by (sort Integer)
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`
   *
   * Apply divisibility-by-k predicate.
   *
   * Parameters:
   *   - 1: Op of kind DIVISIBLE
   *   - 2: Integer Term
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  DIVISIBLE,
  /**
   * Multiple-precision rational constant.
   *
   * Parameters:
   *   See @ref cvc5::api::Solver::mkInteger() "mkInteger()", @ref cvc5::api::Solver::mkReal() "mkReal()".
   *
   * Create with:
   *   - `Solver::mkInteger(const std::string& s) const`
   *   - `Solver::mkInteger(int64_t val) const`
   *   - `Solver::mkReal(const std::string& s) const`
   *   - `Solver::mkReal(int64_t val) const`
   *   - `Solver::mkReal(int64_t num, int64_t den) const`
   */
  CONST_RATIONAL,
  /**
   * Less than, chainable.
   *
   * Parameters: n
   *   - 1..n: Terms of sort Integer, Real; [1] < ... < [n]
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  LT,
  /**
   * Less than or equal, chainable.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer, Real; [1] <= ... <= [n]
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  LEQ,
  /**
   * Greater than, chainable.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer, Real, [1] > ... > [n]
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  GT,
  /**
   * Greater than or equal, chainable.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of sort Integer, Real; [1] >= ... >= [n]
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  GEQ,
  /**
   * Is-integer predicate.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  IS_INTEGER,
  /**
   * Convert Term to Integer by the floor function.
   *
   * Parameters:
   *   - 1: Term of sort Integer, Real
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  TO_INTEGER,
  /**
   * Convert Term to Real.
   *
   * Parameters:
   *
   *   - 1: Term of sort Integer, Real
   *
   * This is a no-op in cvc5, as Integer is a subtype of Real.
   */
  TO_REAL,
  /**
   * Pi constant.
   *
   * Create with:
   *   - `Solver::mkPi() const`
   *   - `Solver::mkTerm(Kind kind) const`
   */
  PI,

  /* BV -------------------------------------------------------------------- */

  /**
   * Fixed-size bit-vector constant.
   *
   * Parameters:
   *   See @ref cvc5::api::Solver::mkBitVector() "mkBitVector()".
   *
   * Create with:
   *   - `Solver::mkBitVector(uint32_t size, uint64_t val) const`
   *   - `Solver::mkBitVector(const std::string& s, uint32_t base) const`
   *   - `Solver::mkBitVector(uint32_t size, const std::string& s, uint32_t base) const`
   */
  CONST_BITVECTOR,
  /**
   * Concatenation of two or more bit-vectors.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_CONCAT,
  /**
   * Bit-wise and.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_AND,
  /**
   * Bit-wise or.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_OR,
  /**
   * Bit-wise xor.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_XOR,
  /**
   * Bit-wise negation.
   *
   * Parameters:
   *   - 1: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BITVECTOR_NOT,
  /**
   * Bit-wise nand.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_NAND,
  /**
   * Bit-wise nor.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_NOR,
  /**
   * Bit-wise xnor, left associative.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_XNOR,
  /**
   * Equality comparison (returns bit-vector of size 1).
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_COMP,
  /**
   * Multiplication of two or more bit-vectors.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_MULT,
  /**
   * Addition of two or more bit-vectors.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_PLUS,
  /**
   * Subtraction of two bit-vectors.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SUB,
  /**
   * Negation of a bit-vector (two's complement).
   *
   * Parameters:
   *   - 1: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BITVECTOR_NEG,
  /**
   * Unsigned division of two bit-vectors, truncating towards 0.
   *
   * Note: The semantics of this operator depends on `bv-div-zero-const`
   * (default is true).  Depending on the setting, a division by zero is
   * treated as all ones (default, corresponds to SMT-LIB >=2.6) or an
   * uninterpreted value (corresponds to SMT-LIB <2.6).
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_UDIV,
  /**
   * Unsigned remainder from truncating division of two bit-vectors.
   *
   * Note: The semantics of this operator depends on `bv-div-zero-const`
   * (default is true). Depending on the setting, if the modulus is zero, the
   * result is either the dividend (default, corresponds to SMT-LIB >=2.6) or
   * an uninterpreted value (corresponds to SMT-LIB <2.6).
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_UREM,
  /**
   * Two's complement signed division of two bit-vectors.
   *
   * Note: The semantics of this operator depends on `bv-div-zero-const`
   * (default is true). By default, the function returns all ones if the
   * dividend is positive and one if the dividend is negative (corresponds to
   * SMT-LIB >=2.6). If the option is disabled, a division by zero is treated
   * as an uninterpreted value (corresponds to SMT-LIB <2.6).
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SDIV,
  /**
   * Two's complement signed remainder of two bit-vectors
   * (sign follows dividend).
   *
   * Note: The semantics of this operator depends on `bv-div-zero-const`
   * (default is true, corresponds to SMT-LIB >=2.6). Depending on the setting,
   * if the modulus is zero, the result is either the dividend (default) or an
   * uninterpreted value (corresponds to SMT-LIB <2.6).
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SREM,
  /**
   * Two's complement signed remainder
   * (sign follows divisor).
   *
   * Note: The semantics of this operator depends on `bv-div-zero-const`
   * (default is on). Depending on the setting, if the modulus is zero, the
   * result is either the dividend (default, corresponds to SMT-LIB >=2.6) or
   * an uninterpreted value (corresponds to SMT-LIB <2.6).
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SMOD,
  /**
   * Bit-vector shift left.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SHL,
  /**
   * Bit-vector logical shift right.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_LSHR,
  /**
   * Bit-vector arithmetic shift right.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_ASHR,
  /**
   * Bit-vector unsigned less than.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_ULT,
  /**
   * Bit-vector unsigned less than or equal.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_ULE,
  /**
   * Bit-vector unsigned greater than.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_UGT,
  /**
   * Bit-vector unsigned greater than or equal.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_UGE,
  /**
   * Bit-vector signed less than.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SLT,
  /**
   * Bit-vector signed less than or equal.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SLE,
  /**
   * Bit-vector signed greater than.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SGT,
  /**
   * Bit-vector signed greater than or equal.
   * The two bit-vector parameters must have same width.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SGE,
  /**
   * Bit-vector unsigned less than, returns bit-vector of size 1.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_ULTBV,
  /**
   * Bit-vector signed less than. returns bit-vector of size 1.
   *
   * Parameters:
   *   - 1..2: Terms of bit-vector sort (sorts must match)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_SLTBV,
  /**
   * Same semantics as regular ITE, but condition is bit-vector of size 1.
   *
   * Parameters:
   *   - 1: Term of bit-vector sort of size 1, representing the condition
   *   - 2: Term reprsenting the 'then' branch
   *   - 3: Term representing the 'else' branch
   *
   * 'then' and 'else' term must have same base sort.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BITVECTOR_ITE,
  /**
   * Bit-vector redor.
   *
   * Parameters:
   *   - 1: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BITVECTOR_REDOR,
  /**
   * Bit-vector redand.
   *
   * Parameters:
   *   - 1: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BITVECTOR_REDAND,
#if 0
  /* formula to be treated as a bv atom via eager bit-blasting
   * (internal-only symbol) */
  BITVECTOR_EAGER_ATOM,
  /* term to be treated as a variable. used for eager bit-blasting Ackermann
   * expansion of bvudiv (internal-only symbol) */
  BITVECTOR_ACKERMANIZE_UDIV,
  /* term to be treated as a variable. used for eager bit-blasting Ackermann
   * expansion of bvurem (internal-only symbol) */
  BITVECTOR_ACKERMANIZE_UREM,
#endif
  /**
   * Operator for bit-vector extract (from index 'high' to 'low').
   *
   * Parameters:
   *   - 1: The 'high' index
   *   - 2: The 'low' index
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param, uint32_t param) const`
   *
   * Apply bit-vector extract.
   *
   * Parameters:
   *   - 1: Op of kind BITVECTOR_EXTRACT
   *   - 2: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  BITVECTOR_EXTRACT,
  /**
   * Operator for bit-vector repeat.
   *
   * Parameter:
   *   - 1: Number of times to repeat a given bit-vector
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`.
   *
   * Apply bit-vector repeat.
   *
   * Parameters:
   *   - 1: Op of kind BITVECTOR_REPEAT
   *   - 2: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  BITVECTOR_REPEAT,
  /**
   * Operator for bit-vector zero-extend.
   *
   * Parameter:
   *   - 1: Number of bits by which a given bit-vector is to be extended
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`.
   *
   * Apply bit-vector zero-extend.
   *
   * Parameters:
   *   - 1: Op of kind BITVECTOR_ZERO_EXTEND
   *   - 2: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  BITVECTOR_ZERO_EXTEND,
  /**
   * Operator for bit-vector sign-extend.
   *
   * Parameter:
   *   - 1: Number of bits by which a given bit-vector is to be extended
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`.
   *
   * Apply bit-vector sign-extend.
   *
   * Parameters:
   *   - 1: Op of kind BITVECTOR_SIGN_EXTEND
   *   - 2: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  BITVECTOR_SIGN_EXTEND,
  /**
   * Operator for bit-vector rotate left.
   *
   * Parameter:
   *   - 1: Number of bits by which a given bit-vector is to be rotated
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`.
   *
   * Apply bit-vector rotate left.
   *
   * Parameters:
   *   - 1: Op of kind BITVECTOR_ROTATE_LEFT
   *   - 2: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  BITVECTOR_ROTATE_LEFT,
  /**
   * Operator for bit-vector rotate right.
   *
   * Parameter:
   *   - 1: Number of bits by which a given bit-vector is to be rotated
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`.
   *
   * Apply bit-vector rotate right.
   *
   * Parameters:
   *   - 1: Op of kind BITVECTOR_ROTATE_RIGHT
   *   - 2: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  BITVECTOR_ROTATE_RIGHT,
#if 0
  /* bit-vector boolean bit extract. */
  BITVECTOR_BITOF,
#endif
  /**
   * Operator for the conversion from Integer to bit-vector.
   *
   * Parameter:
   *   - 1: Size of the bit-vector to convert to
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`.
   *
   * Apply integer conversion to bit-vector.
   *
   * Parameters:
   *   - 1: Op of kind INT_TO_BITVECTOR
   *   - 2: Integer term
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  INT_TO_BITVECTOR,
  /**
   * Bit-vector conversion to (nonnegative) integer.
   *
   * Parameter:
   *   - 1: Term of bit-vector sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BITVECTOR_TO_NAT,

  /* FP -------------------------------------------------------------------- */

  /**
   * Floating-point constant, constructed from a double or string.
   *
   * Parameters:
   *   - 1: Size of the exponent
   *   - 2: Size of the significand
   *   - 3: Value of the floating-point constant as a bit-vector term
   *
   * Create with:
   *   - `Solver::mkFloatingPoint(uint32_t exp, uint32_t sig, Term val) const`
   */
  CONST_FLOATINGPOINT,
  /**
   * Floating-point rounding mode term.
   *
   * Create with:
   *   - `Solver::mkRoundingMode(RoundingMode rm) const`
   */
  CONST_ROUNDINGMODE,
  /**
   * Create floating-point literal from bit-vector triple.
   *
   * Parameters:
   *   - 1: Sign bit as a bit-vector term
   *   - 2: Exponent bits as a bit-vector term
   *   - 3: Significand bits as a bit-vector term (without hidden bit)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_FP,
  /**
   * Floating-point equality.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_EQ,
  /**
   * Floating-point absolute value.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ABS,
  /**
   * Floating-point negation.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_NEG,
  /**
   * Floating-point addition.
   *
   * Parameters:
   *   - 1: CONST_ROUNDINGMODE
   *   - 2: Term of sort FloatingPoint
   *   - 3: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_PLUS,
  /**
   * Floating-point sutraction.
   *
   * Parameters:
   *   - 1: CONST_ROUNDINGMODE
   *   - 2: Term of sort FloatingPoint
   *   - 3: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_SUB,
  /**
   * Floating-point multiply.
   *
   * Parameters:
   *   - 1: CONST_ROUNDINGMODE
   *   - 2: Term of sort FloatingPoint
   *   - 3: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_MULT,
  /**
   * Floating-point division.
   *
   * Parameters:
   *   - 1: CONST_ROUNDINGMODE
   *   - 2: Term of sort FloatingPoint
   *   - 3: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_DIV,
  /**
   * Floating-point fused multiply and add.
   *
   * Parameters:
   *   - 1: CONST_ROUNDINGMODE
   *   - 2: Term of sort FloatingPoint
   *   - 3: Term of sort FloatingPoint
   *   - 4: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_FMA,
  /**
   * Floating-point square root.
   *
   * Parameters:
   *   - 1: CONST_ROUNDINGMODE
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_SQRT,
  /**
   * Floating-point remainder.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_REM,
  /**
   * Floating-point round to integral.
   *
   * Parameters:
   *   -1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_RTI,
  /**
   * Floating-point minimum.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_MIN,
  /**
   * Floating-point maximum.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_MAX,
  /**
   * Floating-point less than or equal.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_LEQ,
  /**
   * Floating-point less than.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_LT,
  /**
   * Floating-point greater than or equal.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_GEQ,
  /**
   * Floating-point greater than.
   *
   * Parameters:
   *   - 1..2: Terms of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_GT,
  /**
   * Floating-point is normal.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISN,
  /**
   * Floating-point is sub-normal.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISSN,
  /**
   * Floating-point is zero.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISZ,
  /**
   * Floating-point is infinite.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISINF,
  /**
   * Floating-point is NaN.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISNAN,
  /**
   * Floating-point is negative.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISNEG,
  /**
   * Floating-point is positive.
   *
   * Parameters:
   *   - 1: Term of floating point sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_ISPOS,
  /**
   * Operator for to_fp from bit vector.
   *
   * Parameters:
   *   - 1: Exponent size
   *   - 2: Significand size
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param1, uint32_t param2) const`
   *
   * Conversion from an IEEE-754 bit vector to floating-point.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_IEEE_BITVECTOR
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
  /**
   * Operator for to_fp from floating point.
   *
   * Parameters:
   *   - 1: Exponent size
   *   - 2: Significand size
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param1, uint32_t param2) const`
   *
   * Conversion between floating-point sorts.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_FLOATINGPOINT
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_FP_FLOATINGPOINT,
  /**
   * Operator for to_fp from real.
   *
   * Parameters:
   *   - 1: Exponent size
   *   - 2: Significand size
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param1, uint32_t param2) const`
   *
   * Conversion from a real to floating-point.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_REAL
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_FP_REAL,
  /**
   * Operator for to_fp from signed bit vector
   *
   * Parameters:
   *   - 1: Exponent size
   *   - 2: Significand size
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param1, uint32_t param2) const`
   *
   * Conversion from a signed bit vector to floating-point.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
  /**
   * Operator for to_fp from unsigned bit vector.
   *
   * Parameters:
   *   - 1: Exponent size
   *   - 2: Significand size
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param1, uint32_t param2) const`
   *
   * Converting an unsigned bit vector to floating-point.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
  /**
   * Operator for a generic to_fp.
   *
   * Parameters:
   *   - 1: exponent size
   *   - 2: Significand size
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param1, uint32_t param2) const`
   *
   * Generic conversion to floating-point, used in parsing only.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_GENERIC
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_FP_GENERIC,
  /**
   * Operator for to_ubv.
   *
   * Parameters:
   *   - 1: Size of the bit-vector to convert to
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`
   *
   * Conversion from a floating-point value to an unsigned bit vector.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_TO_UBV
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_UBV,
  /**
   * Operator for to_sbv.
   *
   * Parameters:
   *   - 1: Size of the bit-vector to convert to
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`
   *
   * Conversion from a floating-point value to a signed bit vector.
   *
   * Parameters:
   *   - 1: Op of kind FLOATINGPOINT_TO_FP_TO_SBV
   *   - 2: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  FLOATINGPOINT_TO_SBV,
  /**
   * Floating-point to real.
   *
   * Parameters:
   *   - 1: Term of sort FloatingPoint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  FLOATINGPOINT_TO_REAL,

  /* Arrays ---------------------------------------------------------------- */

  /**
   * Array select.
   *
   * Parameters:
   *   - 1: Term of array sort
   *   - 2: Selection index
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  SELECT,
  /**
   * Array store.
   *
   * Parameters:
   *   - 1: Term of array sort
   *   - 2: Store index
   *   - 3: Term to store at the index
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  STORE,
  /**
   * Constant array.
   *
   * Parameters:
   *   - 1: Array sort
   *   - 2: Term representing a constant
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   *
   * Note: We currently support the creation of constant arrays, but under some
   * conditions when there is a chain of equalities connecting two constant
   * arrays, the solver doesn't know what to do and aborts (Issue <a href="https://github.com/CVC4/CVC4/issues/1667">#1667</a>).
   */
  CONST_ARRAY,
  /**
   * Equality over arrays a and b over a given range [i,j], i.e.,
   * @f[
   *   \forall k . i \leq k \leq j \Rightarrow a[k] = b[k]
   * @f]
   *
   * Parameters:
   *   - 1: First array
   *   - 2: Second array
   *   - 3: Lower bound of range (inclusive)
   *   - 4: Uppper bound of range (inclusive)
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   *
   * Note: We currently support the creation of array equalities over index
   * types bit-vector, floating-point, integer and real. Option --arrays-exp is
   * required to support this operator.
   */
  EQ_RANGE,
#if 0
  /* array table function (internal-only symbol) */
  ARR_TABLE_FUN,
  /* array lambda (internal-only symbol) */
  ARRAY_LAMBDA,
  /* partial array select, for internal use only */
  PARTIAL_SELECT_0,
  /* partial array select, for internal use only */
  PARTIAL_SELECT_1,
#endif

  /* Datatypes ------------------------------------------------------------- */

  /**
   * Constructor application.
   *
   * Paramters: n > 0
   *   - 1: Constructor (operator)
   *   - 2..n: Parameters to the constructor
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op) const`
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  APPLY_CONSTRUCTOR,
  /**
   * Datatype selector application.
   *
   * Parameters:
   *   - 1: Selector (operator)
   *   - 2: Datatype term (undefined if mis-applied)
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   */
  APPLY_SELECTOR,
  /**
   * Datatype tester application.
   *
   * Parameters:
   *   - 1: Tester term
   *   - 2: Datatype term
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  APPLY_TESTER,
#if 0
  /* Parametric datatype term.  */
  PARAMETRIC_DATATYPE,
  /* type ascription, for datatype constructor applications;
   * first parameter is an ASCRIPTION_TYPE, second is the datatype constructor
   * application being ascribed */
  APPLY_TYPE_ASCRIPTION,
#endif
  /**
   * Operator for a tuple update.
   *
   * Parameters:
   *   - 1: Index of the tuple to be updated
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`
   *
   * Apply tuple update.
   *
   * Parameters:
   *   - 1: Op of kind TUPLE_UPDATE (which references an index)
   *   - 2: Tuple
   *   - 3: Element to store in the tuple at the given index
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  TUPLE_UPDATE,
  /**
   * Operator for a record update.
   *
   * Parameters:
   *   - 1: Name of the field to be updated
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, const std::string& param) const`
   *
   * Record update.
   *
   * Parameters:
   *   - 1: Op of kind RECORD_UPDATE (which references a field)
   *   - 2: Record term to update
   *   - 3: Element to store in the record in the given field
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(const Op& op,, const std::vector<Term>& children) const`
   */
  RECORD_UPDATE,
  /**
   * Match expressions.
   * For example, the smt2 syntax match term
   *   `(match l (((cons h t) h) (nil 0)))`
   * is represented by the AST
   *
   *     (MATCH l
   *       (MATCH_BIND_CASE (BOUND_VAR_LIST h t) (cons h t) h)
   *       (MATCH_CASE nil 0))
   *
   * The type of the last argument of each case term could be equal.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of kind MATCH_CASE or MATCH_BIND_CASE
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   *
   */
  MATCH,
  /**
   * Match case
   * A (constant) case expression to be used within a match expression.
   *
   * Parameters:
   *   - 1: Term denoting the pattern expression
   *   - 2: Term denoting the return value
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  MATCH_CASE,
  /**
   * Match bind case
   * A (non-constant) case expression to be used within a match expression.
   *
   * Parameters:
   *   - 1: a BOUND_VAR_LIST Term containing the free variables of the case
   *   - 2: Term denoting the pattern expression
   *   - 3: Term denoting the return value
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  MATCH_BIND_CASE,
  /**
   * Datatypes size
   * An operator mapping datatypes to an integer denoting the number of
   * non-nullary applications of constructors they contain.
   *
   * Parameters:
   *   - 1: Datatype term
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  DT_SIZE,
  /**
   * Operator for tuple projection indices
   *
   * Parameters:
   *   - 1: The tuple projection indices
   *
   * Create with:
   *   - `Solver::mkOp(Kind TUPLE_PROJECT, std::vector<uint32_t> param) const`
   *
   * Constructs a new tuple from an existing one using the elements at the
   * given indices
   *
   * Parameters:
   *   - 1: a term of tuple sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  TUPLE_PROJECT,
#if 0
  /* datatypes height bound */
  DT_HEIGHT_BOUND,
  /* datatypes height bound */
  DT_SIZE_BOUND,
  /* datatypes sygus bound */
  DT_SYGUS_BOUND,
  /* datatypes sygus term order */
  DT_SYGUS_TERM_ORDER,
  /* datatypes sygus is constant */
  DT_SYGUS_IS_CONST,
#endif

  /* Separation Logic ------------------------------------------------------ */

  /**
   * Separation logic nil term.
   *
   * Parameters: none
   *
   * Create with:
   *   - `Solver::mkSepNil(const Sort& sort) const`
   */
  SEP_NIL,
  /**
   * Separation logic empty heap.
   *
   * Parameters:
   *   - 1: Term of the same sort as the sort of the location of the heap
   *         that is constrained to be empty
   *   - 2: Term of the same sort as the data sort of the heap that is
   *         that is constrained to be empty
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEP_EMP,
  /**
   * Separation logic points-to relation.
   *
   * Parameters:
   *   - 1: Location of the points-to constraint
   *   - 2: Data of the points-to constraint
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEP_PTO,
  /**
   * Separation logic star.
   *
   * Parameters: n > 1
   *   - 1..n: Child constraints that hold in disjoint (separated) heaps
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEP_STAR,
  /**
   * Separation logic magic wand.
   *
   * Parameters:
   *   - 1: Antecendant of the magic wand constraint
   *   - 2: Conclusion of the magic wand constraint, which is asserted to
   *         hold in all heaps that are disjoint extensions of the antecedent.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEP_WAND,
#if 0
  /* separation label (internal use only) */
  SEP_LABEL,
#endif

  /* Sets ------------------------------------------------------------------ */

  /**
   * Empty set constant.
   *
   * Parameters:
   *   - 1: Sort of the set elements
   *
   * Create with:
   *   - `Solver::mkEmptySet(const Sort& sort) const`
   */
  EMPTYSET,
  /**
   * Set union.
   *
   * Parameters:
   *   - 1..2: Terms of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  UNION,
  /**
   * Set intersection.
   *
   * Parameters:
   *   - 1..2: Terms of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INTERSECTION,
  /**
   * Set subtraction.
   *
   * Parameters:
   *   - 1..2: Terms of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SETMINUS,
  /**
   * Subset predicate.
   *
   * Parameters:
   *   - 1..2: Terms of set sort, [1] a subset of set [2]?
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SUBSET,
  /**
   * Set membership predicate.
   *
   * Parameters:
   *   - 1..2: Terms of set sort, [1] a member of set [2]?
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  MEMBER,
  /**
   * Construct a singleton set from an element given as a parameter.
   * The returned set has same type of the element.
   *
   * Parameters:
   *   - 1: Single element
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  SINGLETON,
  /**
   * The set obtained by inserting elements;
   *
   * Parameters: n > 0
   *   - 1..n-1: Elements inserted into set [n]
   *   - n: Set Term
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INSERT,
  /**
   * Set cardinality.
   *
   * Parameters:
   *   - 1: Set to determine the cardinality of
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  CARD,
  /**
   * Set complement with respect to finite universe.
   *
   * Parameters:
   *   - 1: Set to complement
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  COMPLEMENT,
  /**
   * Finite universe set.
   * All set variables must be interpreted as subsets of it.
   *
   * Create with:
   *   - `Solver::mkUniverseSet(const Sort& sort) const`
   */
  UNIVERSE_SET,
  /**
   * Set join.
   *
   * Parameters:
   *   - 1..2: Terms of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  JOIN,
  /**
   * Set cartesian product.
   *
   * Parameters:
   *   - 1..2: Terms of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  PRODUCT,
  /**
   * Set transpose.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  TRANSPOSE,
  /**
   * Set transitive closure.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  TCLOSURE,
  /**
   * Set join image.
   *
   * Parameters:
   *   - 1..2: Terms of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  JOIN_IMAGE,
  /**
   * Set identity.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  IDEN,
  /**
   * Set comprehension
   * A set comprehension is specified by a bound variable list x1 ... xn,
   * a predicate P[x1...xn], and a term t[x1...xn]. A comprehension C with the
   * above form has members given by the following semantics:
   * @f[
   *  \forall y. ( \exists x_1...x_n. P[x_1...x_n] \hat{} t[x_1...x_n] = y )
   * \Leftrightarrow (member y C)
   * @f]
   * where y ranges over the element type of the (set) type of the
   * comprehension. If @f$ t[x_1..x_n] @f$ is not provided, it is equivalent to
   * y in the above formula.
   *
   * Parameters:
   *   - 1: Term BOUND_VAR_LIST
   *   - 2: Term denoting the predicate of the comprehension
   *   - 3: (optional) a Term denoting the generator for the comprehension
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  COMPREHENSION,
  /**
   * Returns an element from a given set.
   * If a set A = {x}, then the term (choose A) is equivalent to the term x.
   * If the set is empty, then (choose A) is an arbitrary value.
   * If the set has cardinality > 1, then (choose A) will deterministically
   * return an element in A.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  CHOOSE,
  /**
   * Set is_singleton predicate.
   *
   * Parameters:
   *   - 1: Term of set sort, is [1] a singleton set?
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  IS_SINGLETON,
  /* Bags ------------------------------------------------------------------ */
  /**
   * Empty bag constant.
   *
   * Parameters:
   *   - 1: Sort of the bag elements
   *
   * Create with:
   *   mkEmptyBag(const Sort& sort)
   */
  EMPTYBAG,
  /**
   * Bag max union.
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  UNION_MAX,
  /**
   * Bag disjoint union (sum).
   *
   * Parameters:
   *   -1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  UNION_DISJOINT,
  /**
   * Bag intersection (min).
   *
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INTERSECTION_MIN,
  /**
   * Bag difference subtract (subtracts multiplicities of the second from the
   * first).
   *
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  DIFFERENCE_SUBTRACT,
  /**
   * Bag difference 2 (removes shared elements in the two bags).
   *
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  DIFFERENCE_REMOVE,
  /**
   * Inclusion predicate for bags
   * (multiplicities of the first bag <= multiplicities of the second bag).
   *
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SUBBAG,
  /**
   * Element multiplicity in a bag
   *
   * Parameters:
   *   - 1..2: Terms of bag sort (Bag E), [1] an element of sort E
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BAG_COUNT,
  /**
   * Eliminate duplicates in a given bag. The returned bag contains exactly the
   * same elements in the given bag, but with multiplicity one.
   *
   * Parameters:
   *   - 1: a term of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  DUPLICATE_REMOVAL,
  /**
   * The bag of the single element given as a parameter.
   *
   * Parameters:
   *   - 1: Single element
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  MK_BAG,
  /**
   * Bag cardinality.
   *
   * Parameters:
   *   - 1: Bag to determine the cardinality of
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BAG_CARD,
  /**
   * Returns an element from a given bag.
   * If a bag A = {(x,n)} where n is the multiplicity, then the term (choose A)
   * is equivalent to the term x.
   * If the bag is empty, then (choose A) is an arbitrary value.
   * If the bag contains distinct elements, then (choose A) will
   * deterministically return an element in A.
   *
   * Parameters:
   *   - 1: Term of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BAG_CHOOSE,
  /**
   * Bag is_singleton predicate (single element with multiplicity exactly one).
   * Parameters:
   *   - 1: Term of bag sort, is [1] a singleton bag?
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BAG_IS_SINGLETON,
  /**
   * Bag.from_set converts a set to a bag.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BAG_FROM_SET,
  /**
   * Bag.to_set converts a bag to a set.
   *
   * Parameters:
   *   - 1: Term of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  BAG_TO_SET,

  /* Strings --------------------------------------------------------------- */

  /**
   * String concat.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of String sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_CONCAT,
  /**
   * String membership.
   *
   * Parameters:
   *   - 1: Term of String sort
   *   - 2: Term of RegExp sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_IN_REGEXP,
  /**
   * String length.
   *
   * Parameters:
   *   - 1: Term of String sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_LENGTH,
  /**
   * String substring.
   * Extracts a substring, starting at index i and of length l, from a string
   * s.  If the start index is negative, the start index is greater than the
   * length of the string, or the length is negative, the result is the empty
   * string.
   *
   * Parameters:
   *   - 1: Term of sort String
   *   - 2: Term of sort Integer (index i)
   *   - 3: Term of sort Integer (length l)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_SUBSTR,
  /**
   * String update.
   * Updates a string s by replacing its context starting at an index with t.
   * If the start index is negative, the start index is greater than the
   * length of the string, the result is s. Otherwise, the length of the
   * original string is preserved.
   *
   * Parameters:
   *   - 1: Term of sort String
   *   - 2: Term of sort Integer (index i)
   *   - 3: Term of sort String (replacement string t)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_UPDATE,
  /**
   * String character at.
   * Returns the character at index i from a string s. If the index is negative
   * or the index is greater than the length of the string, the result is the
   * empty string. Otherwise the result is a string of length 1.
   *
   * Parameters:
   *   - 1: Term of sort String (string s)
   *   - 2: Term of sort Integer (index i)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_CHARAT,
  /**
   * String contains.
   * Checks whether a string s1 contains another string s2. If s2 is empty, the
   * result is always true.
   *
   * Parameters:
   *   - 1: Term of sort String (the string s1)
   *   - 2: Term of sort String (the string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_CONTAINS,
  /**
   * String index-of.
   * Returns the index of a substring s2 in a string s1 starting at index i. If
   * the index is negative or greater than the length of string s1 or the
   * substring s2 does not appear in string s1 after index i, the result is -1.
   *
   * Parameters:
   *   - 1: Term of sort String (substring s1)
   *   - 2: Term of sort String (substring s2)
   *   - 3: Term of sort Integer (index i)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_INDEXOF,
  /**
   * String replace.
   * Replaces a string s2 in a string s1 with string s3. If s2 does not appear
   * in s1, s1 is returned unmodified.
   *
   * Parameters:
   *   - 1: Term of sort String (string s1)
   *   - 2: Term of sort String (string s2)
   *   - 3: Term of sort String (string s3)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_REPLACE,
  /**
   * String replace all.
   * Replaces all occurrences of a string s2 in a string s1 with string s3.
   * If s2 does not appear in s1, s1 is returned unmodified.
   *
   * Parameters:
   *   - 1: Term of sort String (string s1)
   *   - 2: Term of sort String (string s2)
   *   - 3: Term of sort String (string s3)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_REPLACE_ALL,
  /**
   * String replace regular expression match.
   * Replaces the first match of a regular expression r in string s1 with
   * string s2. If r does not match a substring of s1, s1 is returned
   * unmodified.
   *
   * Parameters:
   *   - 1: Term of sort String (string s1)
   *   - 2: Term of sort Regexp (regexp r)
   *   - 3: Term of sort String (string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_REPLACE_RE,
  /**
   * String replace all regular expression matches.
   * Replaces all matches of a regular expression r in string s1 with string
   * s2. If r does not match a substring of s1, s1 is returned unmodified.
   *
   * Parameters:
   *   - 1: Term of sort String (string s1)
   *   - 2: Term of sort Regexp (regexp r)
   *   - 3: Term of sort String (string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_REPLACE_RE_ALL,
  /**
   * String to lower case.
   *
   * Parameters:
   *   - 1: Term of String sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_TOLOWER,
  /**
   * String to upper case.
   *
   * Parameters:
   *   - 1: Term of String sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_TOUPPER,
  /**
   * String reverse.
   *
   * Parameters:
   *   - 1: Term of String sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_REV,
  /**
   * String to code.
   * Returns the code point of a string if it has length one, or returns -1
   * otherwise.
   *
   * Parameters:
   *   - 1: Term of String sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_TO_CODE,
  /**
   * String from code.
   * Returns a string containing a single character whose code point matches
   * the argument to this function, or the empty string if the argument is
   * out-of-bounds.
   *
   * Parameters:
   *   - 1: Term of Integer sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_FROM_CODE,
  /**
   * String less than.
   * Returns true if string s1 is (strictly) less than s2 based on a
   * lexiographic ordering over code points.
   *
   * Parameters:
   *   - 1: Term of sort String (the string s1)
   *   - 2: Term of sort String (the string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_LT,
  /**
   * String less than or equal.
   * Returns true if string s1 is less than or equal to s2 based on a
   * lexiographic ordering over code points.
   *
   * Parameters:
   *   - 1: Term of sort String (the string s1)
   *   - 2: Term of sort String (the string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_LEQ,
  /**
   * String prefix-of.
   * Checks whether a string s1 is a prefix of string s2. If string s1 is
   * empty, this operator returns true.
   *
   * Parameters:
   *   - 1: Term of sort String (string s1)
   *   - 2: Term of sort String (string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_PREFIX,
  /**
   * String suffix-of.
   * Checks whether a string s1 is a suffix of string 2. If string s1 is empty,
   * this operator returns true.
   *
   * Parameters:
   *   - 1: Term of sort String (string s1)
   *   - 2: Term of sort String (string s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_SUFFIX,
  /**
   * String is-digit.
   * Returns true if string s is digit (it is one of "0", ..., "9").
   *
   * Parameters:
   *   - 1: Term of sort String
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_IS_DIGIT,
  /**
   * Integer to string.
   * If the integer is negative this operator returns the empty string.
   *
   * Parameters:
   *   - 1: Term of sort Integer
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_FROM_INT,
  /**
   * String to integer (total function).
   * If the string does not contain an integer or the integer is negative, the
   * operator returns -1.
   *
   * Parameters:
   *   - 1: Term of sort String
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_TO_INT,
  /**
   * Constant string.
   *
   * Parameters:
   *   - See @ref cvc5::api::Solver::mkString() "mkString()".
   *
   * Create with:
   *   - `Solver::mkString(const std::string& s, bool useEscSequences) const`
   *   - `Solver::mkString(const unsigned char c) const`
   *   - `Solver::mkString(const std::vector<uint32_t>& s) const`
   */
  CONST_STRING,
  /**
   * Conversion from string to regexp.
   *
   * Parameters:
   *   - 1: Term of sort String
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  STRING_TO_REGEXP,
  /**
   * Regexp Concatenation.
   *
   * Parameters:
   *   - 1..2: Terms of Regexp sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  REGEXP_CONCAT,
  /**
   * Regexp union.
   *
   * Parameters:
   *   - 1..2: Terms of Regexp sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  REGEXP_UNION,
  /**
   * Regexp intersection.
   *
   * Parameters:
   *   - 1..2: Terms of Regexp sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  REGEXP_INTER,
  /**
   * Regexp difference.
   *
   * Parameters:
   *   - 1..2: Terms of Regexp sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  REGEXP_DIFF,
  /**
   * Regexp *.
   *
   * Parameters:
   *   - 1: Term of sort Regexp
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  REGEXP_STAR,
  /**
   * Regexp +.
   *
   * Parameters:
   *   - 1: Term of sort Regexp
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  REGEXP_PLUS,
  /**
   * Regexp ?.
   *
   * Parameters:
   *   - 1: Term of sort Regexp
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  REGEXP_OPT,
  /**
   * Regexp range.
   *
   * Parameters:
   *   - 1: Lower bound character for the range
   *   - 2: Upper bound character for the range
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  REGEXP_RANGE,
  /**
   * Operator for regular expression repeat.
   *
   * Parameters:
   *   - 1: The number of repetitions
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param) const`
   *
   * Apply regular expression loop.
   *
   * Parameters:
   *   - 1: Op of kind REGEXP_REPEAT
   *   - 2: Term of regular expression sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  REGEXP_REPEAT,
  /**
   * Operator for regular expression loop, from lower bound to upper bound
   * number of repetitions.
   *
   * Parameters:
   *   - 1: The lower bound
   *   - 2: The upper bound
   *
   * Create with:
   *   - `Solver::mkOp(Kind kind, uint32_t param, uint32_t param) const`
   *
   * Apply regular expression loop.
   *
   * Parameters:
   *   - 1: Op of kind REGEXP_LOOP
   *   - 2: Term of regular expression sort
   *
   * Create with:
   *   - `Solver::mkTerm(const Op& op, const Term& child) const`
   *   - `Solver::mkTerm(const Op& op, const std::vector<Term>& children) const`
   */
  REGEXP_LOOP,
  /**
   * Regexp empty.
   *
   * Parameters: none
   *
   * Create with:
   *   - `Solver::mkRegexpEmpty() const`
   *   - `Solver::mkTerm(Kind kind) const`
   */
  REGEXP_EMPTY,
  /**
   * Regexp all characters.
   *
   * Parameters: none
   *
   * Create with:
   *   - `Solver::mkRegexpSigma() const`
   *   - `Solver::mkTerm(Kind kind) const`
   */
  REGEXP_SIGMA,
  /**
   * Regexp complement.
   *
   * Parameters:
   *   - 1: Term of sort RegExp
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1) const`
   */
  REGEXP_COMPLEMENT,

  /**
   * Sequence concat.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of Sequence sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_CONCAT,
  /**
   * Sequence length.
   *
   * Parameters:
   *   - 1: Term of Sequence sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  SEQ_LENGTH,
  /**
   * Sequence extract.
   * Extracts a subsequence, starting at index i and of length l, from a
   * sequence s.  If the start index is negative, the start index is greater
   * than the length of the sequence, or the length is negative, the result is
   * the empty sequence.
   *
   * Parameters:
   *   - 1: Term of sort Sequence
   *   - 2: Term of sort Integer (index i)
   *   - 3: Term of sort Integer (length l)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_EXTRACT,
  /**
   * Sequence update.
   * Updates a sequence s by replacing its context starting at an index with t.
   * If the start index is negative, the start index is greater than the
   * length of the sequence, the result is s. Otherwise, the length of the
   * original sequence is preserved.
   *
   * Parameters:
   *   - 1: Term of sort Sequence
   *   - 2: Term of sort Integer (index i)
   *   - 3: Term of sort Sequence (replacement sequence t)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_UPDATE,
  /**
   * Sequence element at.
   * Returns the element at index i from a sequence s. If the index is negative
   * or the index is greater or equal to the length of the sequence, the result
   * is the empty sequence. Otherwise the result is a sequence of length 1.
   *
   * Parameters:
   *   - 1: Term of sequence sort (string s)
   *   - 2: Term of sort Integer (index i)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_AT,
  /**
   * Sequence contains.
   * Checks whether a sequence s1 contains another sequence s2. If s2 is empty,
   * the result is always true.
   *
   * Parameters:
   *   - 1: Term of sort Sequence (the sequence s1)
   *   - 2: Term of sort Sequence (the sequence s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_CONTAINS,
  /**
   * Sequence index-of.
   * Returns the index of a subsequence s2 in a sequence s1 starting at index i.
   * If the index is negative or greater than the length of sequence s1 or the
   * subsequence s2 does not appear in sequence s1 after index i, the result is
   * -1.
   *
   * Parameters:
   *   - 1: Term of sort Sequence (subsequence s1)
   *   - 2: Term of sort Sequence (subsequence s2)
   *   - 3: Term of sort Integer (index i)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_INDEXOF,
  /**
   * Sequence replace.
   * Replaces the first occurrence of a sequence s2 in a sequence s1 with
   * sequence s3. If s2 does not appear in s1, s1 is returned unmodified.
   *
   * Parameters:
   *   - 1: Term of sort Sequence (sequence s1)
   *   - 2: Term of sort Sequence (sequence s2)
   *   - 3: Term of sort Sequence (sequence s3)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_REPLACE,
  /**
   * Sequence replace all.
   * Replaces all occurrences of a sequence s2 in a sequence s1 with sequence
   * s3. If s2 does not appear in s1, s1 is returned unmodified.
   *
   * Parameters:
   *   - 1: Term of sort Sequence (sequence s1)
   *   - 2: Term of sort Sequence (sequence s2)
   *   - 3: Term of sort Sequence (sequence s3)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_REPLACE_ALL,
  /**
   * Sequence reverse.
   *
   * Parameters:
   *   - 1: Term of Sequence sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  SEQ_REV,
  /**
   * Sequence prefix-of.
   * Checks whether a sequence s1 is a prefix of sequence s2. If sequence s1 is
   * empty, this operator returns true.
   *
   * Parameters:
   *   - 1: Term of sort Sequence (sequence s1)
   *   - 2: Term of sort Sequence (sequence s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_PREFIX,
  /**
   * Sequence suffix-of.
   * Checks whether a sequence s1 is a suffix of sequence s2. If sequence s1 is
   * empty, this operator returns true.
   *
   * Parameters:
   *   - 1: Term of sort Sequence (sequence s1)
   *   - 2: Term of sort Sequence (sequence s2)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  SEQ_SUFFIX,
  /**
   * Constant sequence.
   *
   * Parameters:
   *   - See @ref cvc5::api::Solver::mkEmptySequence() "mkEmptySequence()".
   *
   * Create with:
   *   - `Solver::mkEmptySequence(const Sort& sort) const`
   *
   * Note that a constant sequence is a term that is equivalent to:
   *
   *     (seq.++ (seq.unit c1) ... (seq.unit cn))
   *
   * where n>=0 and c1, ..., cn are constants of some sort. The elements
   * can be extracted by `Term::getConstSequenceElements()`.
   */
  CONST_SEQUENCE,
  /**
   * Sequence unit, corresponding to a sequence of length one with the given
   * term.
   *
   * Parameters:
   *   - 1: Element term.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1) const`
   */
  SEQ_UNIT,
  /**
   * Sequence nth, corresponding to the nth element of a sequence.
   *
   * Parameters:
   *   - 1: Sequence term.
   *   - 2: Integer term.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   */
  SEQ_NTH,

  /* Quantifiers ----------------------------------------------------------- */

  /**
   * Universally quantified formula.
   *
   * Parameters:
   *   - 1: BOUND_VAR_LIST Term
   *   - 2: Quantifier body
   *   - 3: (optional) INST_PATTERN_LIST Term
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  FORALL,
  /**
   * Existentially quantified formula.
   *
   * Parameters:
   *   - 1: BOUND_VAR_LIST Term
   *   - 2: Quantifier body
   *   - 3: (optional) INST_PATTERN_LIST Term
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  EXISTS,
  /**
   * A list of bound variables (used to bind variables under a quantifier)
   *
   * Parameters: n > 1
   *   - 1..n: Terms with kind BOUND_VARIABLE
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BOUND_VAR_LIST,
  /**
   * An instantiation pattern.
   * Specifies a (list of) terms to be used as a pattern for quantifier
   * instantiation.
   *
   * Parameters: n > 1
   *   - 1..n: Terms with kind BOUND_VARIABLE
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INST_PATTERN,
  /**
   * An instantiation no-pattern.
   * Specifies a (list of) terms that should not be used as a pattern for
   * quantifier instantiation.
   *
   * Parameters: n > 1
   *   - 1..n: Terms with kind BOUND_VARIABLE
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INST_NO_PATTERN,
  /*
   * An instantiation pool.
   * Specifies an annotation for pool based instantiation.
   * Parameters: n > 1
   *   - 1..n: Terms that comprise the pools, which are one-to-one with
   * the variables of the quantified formula to be instantiated.
   * Create with:
   *   - `mkTerm(Kind kind, Term child1, Term child2)
   *   - `mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   - `mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INST_POOL,
  /*
   * A instantantiation-add-to-pool annotation.
   * Parameters: n = 1
   *   - 1: The pool to add to.
   * Create with:
   *   - `mkTerm(Kind kind, Term child)
   */
  INST_ADD_TO_POOL,
  /*
   * A skolemization-add-to-pool annotation.
   * Parameters: n = 1
   *   - 1: The pool to add to.
   * Create with:
   *   - `mkTerm(Kind kind, Term child)
   */
  SKOLEM_ADD_TO_POOL,
  /**
   * An instantiation attribute
   * Specifies a custom property for a quantified formula given by a
   * term that is ascribed a user attribute.
   *
   * Parameters:
   *   - 1: Term with a user attribute.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  INST_ATTRIBUTE,
  /**
   * A list of instantiation patterns and/or attributes.
   *
   * Parameters: n > 1
   *   - 1..n: Terms with kind INST_PATTERN, INST_NO_PATTERN, or
   * INST_ATTRIBUTE.
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  INST_PATTERN_LIST,
#if 0

  /* Sort Kinds ------------------------------------------------------------ */

  /* array type */
   ARRAY_TYPE,
  /* a type parameter for type ascription */
  ASCRIPTION_TYPE,
  /* constructor */
  CONSTRUCTOR_TYPE,
  /* a datatype type index */
  DATATYPE_TYPE,
  /* selector */
  SELECTOR_TYPE,
  /* set type, takes as parameter the type of the elements */
  SET_TYPE,
  /* bag type, takes as parameter the type of the elements */
  BAG_TYPE,
  /* sort tag */
  SORT_TAG,
  /* specifies types of user-declared 'uninterpreted' sorts */
  SORT_TYPE,
  /* tester */
  TESTER_TYPE,
  /* a representation for basic types */
  TYPE_CONSTANT,
  /* a function type */
  FUNCTION_TYPE,
  /* the type of a symbolic expression */
  SEXPR_TYPE,
  /* bit-vector type */
  BITVECTOR_TYPE,
  /* floating-point type */
  FLOATINGPOINT_TYPE,
#endif

  /* ----------------------------------------------------------------------- */
  /** Marks the upper-bound of this enumeration. */
  LAST_KIND
};

/**
 * Get the string representation of a given kind.
 * @param k the kind
 * @return the string representation of kind k
 */
std::string kindToString(Kind k) CVC5_EXPORT;

/**
 * Serialize a kind to given stream.
 * @param out the output stream
 * @param k the kind to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, Kind k) CVC5_EXPORT;

}  // namespace api
}  // namespace cvc5

namespace std {

/**
 * Hash function for Kinds.
 */
template<>
struct CVC5_EXPORT hash<cvc5::api::Kind>
{
  /**
   * Hashes a Kind to a size_t.
   */
  size_t operator()(cvc5::api::Kind k) const;
};

}

#endif
