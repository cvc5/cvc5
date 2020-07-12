/*********************                                                        */
/*! \file cvc4cppkind.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds, Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The term kinds of the CVC4 C++ API.
 **
 ** The term kinds of the CVC4 C++ API.
 **/

#include "cvc4_public.h"

#ifndef CVC4__API__CVC4CPPKIND_H
#define CVC4__API__CVC4CPPKIND_H

#include <ostream>

namespace CVC4 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

/**
 * The kind of a CVC4 term.
 *
 * Note that the underlying type of Kind must be signed (to enable range
 * checks for validity). The size of this type depends on the size of
 * CVC4::Kind (NodeValue::NBITS_KIND, currently 10 bits, see expr/node_value.h).
 */
enum CVC4_PUBLIC Kind : int32_t
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
   * Null kind (kind of null term Term()).
   * Do not explicitly create via API functions other than Term().
   */
  NULL_EXPR,

  /* Builtin --------------------------------------------------------------- */

  /**
   * Uninterpreted constant.
   * Parameters: 2
   *   -[1]: Sort of the constant
   *   -[2]: Index of the constant
   * Create with:
   *   mkUninterpretedConst(Sort sort, int32_t index)
   */
  UNINTERPRETED_CONSTANT,
  /**
   * Abstract value (other than uninterpreted sort constants).
   * Parameters: 1
   *   -[1]: Index of the abstract value
   * Create with:
   *   mkAbstractValue(const std::string& index);
   *   mkAbstractValue(uint64_t index);
   */
  ABSTRACT_VALUE,
#if 0
  /* Built-in operator */
  BUILTIN,
#endif
  /**
   * Equality, chainable.
   * Parameters: n > 1
   *   -[1]..[n]: Terms with same sorts
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  EQUAL,
  /**
   * Disequality.
   * Parameters: n > 1
   *   -[1]..[n]: Terms with same sorts
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DISTINCT,
  /**
   * First-order constant.
   * Not permitted in bindings (forall, exists, ...).
   * Parameters:
   *   See mkConst().
   * Create with:
   *   mkConst(const std::string& symbol, Sort sort)
   *   mkConst(Sort sort)
   */
  CONSTANT,
  /**
   * (Bound) variable.
   * Permitted in bindings and in the lambda and quantifier bodies only.
   * Parameters:
   *   See mkVar().
   * Create with:
   *   mkVar(const std::string& symbol, Sort sort)
   *   mkVar(Sort sort)
   */
  VARIABLE,
#if 0
  /* Skolem variable (internal only) */
  SKOLEM,
  /* Symbolic expression (any arity) */
  SEXPR,
#endif
  /**
   * Lambda expression.
   * Parameters: 2
   *   -[1]: BOUND_VAR_LIST
   *   -[2]: Lambda body
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  LAMBDA,
  /**
   * The syntax of a witness term is similar to a quantified formula except that
   * only one bound variable is allowed.
   * The term (witness ((x T)) F) returns an element x of type T
   * and asserts F.
   *
   * The witness operator behaves like the description operator
   * (see https://planetmath.org/hilbertsvarepsilonoperator) if there is no x
   * that satisfies F. But if such x exists, the witness operator does not
   * enforce the axiom that ensures uniqueness up to logical equivalence:
   * forall x. F \equiv G => witness x. F =  witness x. G
   *
   * For example if there are 2 elements of type T that satisfy F, then the
   * following formula is satisfiable:
   * (distinct
   *    (witness ((x Int)) F)
   *    (witness ((x Int)) F))
   *
   * This kind is primarily used internally, but may be returned in models
   * (e.g. for arithmetic terms in non-linear queries). However, it is not
   * supported by the parser. Moreover, the user of the API should be cautious
   * when using this operator. In general, all witness terms
   * (witness ((x Int)) F) should be such that (exists ((x Int)) F) is a valid
   * formula. If this is not the case, then the semantics in formulas that use
   * witness terms may be unintuitive. For example, the following formula is
   * unsatisfiable:
   * (or (= (witness ((x Int)) false) 0) (not (= (witness ((x Int)) false) 0))
   * whereas notice that (or (= z 0) (not (= z 0))) is true for any z.
   *
   * Parameters: 2
   *   -[1]: BOUND_VAR_LIST
   *   -[2]: Witness body
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  WITNESS,

  /* Boolean --------------------------------------------------------------- */

  /**
   * Boolean constant.
   * Parameters: 1
   *   -[1]: Boolean value of the constant
   * Create with:
   *   mkTrue()
   *   mkFalse()
   *   mkBoolean(bool val)
   */
  CONST_BOOLEAN,
  /* Logical not.
   * Parameters: 1
   *   -[1]: Boolean Term to negate
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  NOT,
  /* Logical and.
   * Parameters: n > 1
   *   -[1]..[n]: Boolean Term of the conjunction
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  AND,
  /**
   * Logical implication.
   * Parameters: n > 1
   *   -[1]..[n]: Boolean Terms, right associative
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  IMPLIES,
  /* Logical or.
   * Parameters: n > 1
   *   -[1]..[n]: Boolean Term of the disjunction
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  OR,
  /* Logical exclusive or, left associative.
   * Parameters: n > 1
   *   -[1]..[n]: Boolean Terms, [1] xor ... xor [n]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  XOR,
  /* If-then-else.
   * Parameters: 3
   *   -[1] is a Boolean condition Term
   *   -[2] the 'then' Term
   *   -[3] the 'else' Term
   * 'then' and 'else' term must have same base sort.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  ITE,

  /* UF -------------------------------------------------------------------- */

  /* Application of an uninterpreted function.
   * Parameters: n > 1
   *   -[1]: Function Term
   *   -[2]..[n]: Function argument instantiation Terms
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
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
   * Parameters: 2
   *   -[1]: Term of sort S
   *   -[2]: Positive integer constant that bounds the cardinality of sort S
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  CARDINALITY_CONSTRAINT,
  /*
   * Cardinality value for uninterpreted sort S.
   * An operator that returns an integer indicating the value of the cardinality
   * of sort S.
   * Parameters: 1
   *   -[1]: Term of sort S
   * Create with:
   *   mkTerm(Kind kind, Term child1)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
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
   * Parameters: n > 1
   *   -[1]: Function to apply
   *   -[2] ... [n]: Arguments of the function
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  HO_APPLY,

  /* Arithmetic ------------------------------------------------------------ */

  /**
   * Arithmetic addition.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer, Real (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  PLUS,
  /**
   * Arithmetic multiplication.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer, Real (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MULT,
  /**
   * Operator for Integer AND
   * Parameter: 1
   *   -[1]: Size of the bit-vector that determines the semantics of the IAND
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply integer conversion to bit-vector.
   * Parameters: 2
   *   -[1]: Op of kind IAND
   *   -[2]: Integer term
   *   -[3]: Integer term
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  IAND,
#if 0
  /* Synonym for MULT.  */
  NONLINEAR_MULT,
#endif
  /**
   * Arithmetic subtraction, left associative.
   * Parameters: n
   *   -[1]..[n]: Terms of sort Integer, Real (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MINUS,
  /**
   * Arithmetic negation.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  UMINUS,
  /**
   * Real division, division by 0 undefined, left associative.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DIVISION,
  /**
   * Integer division, division by 0 undefined, left associative.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTS_DIVISION,
  /**
   * Integer modulus, division by 0 undefined.
   * Parameters: 2
   *   -[1]..[2]: Terms of sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTS_MODULUS,
  /**
   * Absolute value.
   * Parameters: 1
   *   -[1]: Term of sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ABS,
  /**
   * Arithmetic power.
   * Parameters: 2
   *   -[1]..[2]: Terms of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  POW,
  /**
   * Exponential.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  EXPONENTIAL,
  /**
   * Sine.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SINE,
  /**
   * Cosine.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COSINE,
  /**
   * Tangent.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TANGENT,
  /**
   * Cosecant.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COSECANT,
  /**
   * Secant.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SECANT,
  /**
   * Cotangent.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COTANGENT,
  /**
   * Arc sine.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCSINE,
  /**
   * Arc cosine.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCCOSINE,
  /**
   * Arc tangent.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCTANGENT,
  /**
   * Arc cosecant.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCCOSECANT,
  /**
   * Arc secant.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCSECANT,
  /**
   * Arc cotangent.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  ARCCOTANGENT,
  /**
   * Square root.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SQRT,
  /**
   * Operator for the divisibility-by-k predicate.
   * Parameter: 1
   *   -[1]: The k to divide by (sort Integer)
   * Create with:
   *   mkOp(Kind kind, uint32_t param)
   *
   * Apply divisibility-by-k predicate.
   * Parameters: 2
   *   -[1]: Op of kind DIVISIBLE
   *   -[2]: Integer Term
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  DIVISIBLE,
  /**
   * Multiple-precision rational constant.
   * Parameters:
   *   See mkInteger(), mkReal(), mkRational()
   * Create with:
   *   mkInteger(const char* s, uint32_t base = 10)
   *   mkInteger(const std::string& s, uint32_t base = 10)
   *   mkInteger(int32_t val)
   *   mkInteger(uint32_t val)
   *   mkInteger(int64_t val)
   *   mkInteger(uint64_t val)
   *   mkReal(const char* s, uint32_t base = 10)
   *   mkReal(const std::string& s, uint32_t base = 10)
   *   mkReal(int32_t val)
   *   mkReal(int64_t val)
   *   mkReal(uint32_t val)
   *   mkReal(uint64_t val)
   *   mkReal(int32_t num, int32_t den)
   *   mkReal(int64_t num, int64_t den)
   *   mkReal(uint32_t num, uint32_t den)
   *   mkReal(uint64_t num, uint64_t den)
   */
  CONST_RATIONAL,
  /**
   * Less than, chainable.
   * Parameters: n
   *   -[1]..[n]: Terms of sort Integer, Real; [1] < ... < [n]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  LT,
  /**
   * Less than or equal, chainable.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer, Real; [1] <= ... <= [n]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  LEQ,
  /**
   * Greater than, chainable.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer, Real, [1] > ... > [n]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  GT,
  /**
   * Greater than or equal, chainable.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of sort Integer, Real; [1] >= ... >= [n]
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  GEQ,
  /**
   * Is-integer predicate.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  IS_INTEGER,
  /**
   * Convert Term to Integer by the floor function.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TO_INTEGER,
  /**
   * Convert Term to Real.
   * Parameters: 1
   *   -[1]: Term of sort Integer, Real
   * This is a no-op in CVC4, as Integer is a subtype of Real.
   */
  TO_REAL,
  /**
   * Pi constant.
   * Create with:
   *   mkPi()
   *   mkTerm(Kind kind)
   */
  PI,

  /* BV -------------------------------------------------------------------- */

  /**
   * Fixed-size bit-vector constant.
   * Parameters:
   *   See mkBitVector().
   * Create with:
   *   mkBitVector(uint32_t size, uint64_t val)
   *   mkBitVector(const char* s, uint32_t base = 2)
   *   mkBitVector(std::string& s, uint32_t base = 2)
   */
  CONST_BITVECTOR,
  /**
   * Concatenation of two or more bit-vectors.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_CONCAT,
  /**
   * Bit-wise and.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_AND,
  /**
   * Bit-wise or.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_OR,
  /**
   * Bit-wise xor.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_XOR,
  /**
   * Bit-wise negation.
   * Parameters: 1
   *   -[1]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_NOT,
  /**
   * Bit-wise nand.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_NAND,
  /**
   * Bit-wise nor.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_NOR,
  /**
   * Bit-wise xnor, left associative.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_XNOR,
  /**
   * Equality comparison (returns bit-vector of size 1).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_COMP,
  /**
   * Multiplication of two or more bit-vectors.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_MULT,
  /**
   * Addition of two or more bit-vectors.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_PLUS,
  /**
   * Subtraction of two bit-vectors.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SUB,
  /**
   * Negation of a bit-vector (two's complement).
   * Parameters: 1
   *   -[1]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_NEG,
  /**
   * Unsigned division of two bit-vectors, truncating towards 0.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UDIV,
  /**
   * Unsigned remainder from truncating division of two bit-vectors.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UREM,
  /**
   * Two's complement signed division of two bit-vectors.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SDIV,
  /**
   * Two's complement signed remainder of two bit-vectors
   * (sign follows dividend).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SREM,
  /**
   * Two's complement signed remainder
   * (sign follows divisor).
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SMOD,
  /**
   * Bit-vector shift left.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SHL,
  /**
   * Bit-vector logical shift right.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_LSHR,
  /**
   * Bit-vector arithmetic shift right.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ASHR,
  /**
   * Bit-vector unsigned less than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ULT,
  /**
   * Bit-vector unsigned less than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ULE,
  /**
   * Bit-vector unsigned greater than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UGT,
  /**
   * Bit-vector unsigned greater than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_UGE,
  /* Bit-vector signed less than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SLT,
  /**
   * Bit-vector signed less than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SLE,
  /**
   * Bit-vector signed greater than.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SGT,
  /**
   * Bit-vector signed greater than or equal.
   * The two bit-vector parameters must have same width.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SGE,
  /**
   * Bit-vector unsigned less than, returns bit-vector of size 1.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ULTBV,
  /**
   * Bit-vector signed less than. returns bit-vector of size 1.
   * Parameters: 2
   *   -[1]..[2]: Terms of bit-vector sort (sorts must match)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_SLTBV,
  /**
   * Same semantics as regular ITE, but condition is bit-vector of size 1.
   * Parameters: 3
   *   -[1]: Term of bit-vector sort of size 1, representing the condition
   *   -[2]: Term reprsenting the 'then' branch
   *   -[3]: Term representing the 'else' branch
   * 'then' and 'else' term must have same base sort.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BITVECTOR_ITE,
  /**
   * Bit-vector redor.
   * Parameters: 1
   *   -[1]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_REDOR,
  /**
   * Bit-vector redand.
   * Parameters: 1
   *   -[1]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
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
   * Parameters: 2
   *   -[1]: The 'high' index
   *   -[2]: The 'low' index
   * Create with:
   *   mkOp(Kind kind, uint32_t param, uint32_t param)
   *
   * Apply bit-vector extract.
   * Parameters: 2
   *   -[1]: Op of kind BITVECTOR_EXTRACT
   *   -[2]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  BITVECTOR_EXTRACT,
  /**
   * Operator for bit-vector repeat.
   * Parameter 1:
   *   -[1]: Number of times to repeat a given bit-vector
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply bit-vector repeat.
   * Parameters: 2
   *   -[1]: Op of kind BITVECTOR_REPEAT
   *   -[2]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  BITVECTOR_REPEAT,
  /**
   * Operator for bit-vector zero-extend.
   * Parameter 1:
   *   -[1]: Number of bits by which a given bit-vector is to be extended
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply bit-vector zero-extend.
   * Parameters: 2
   *   -[1]: Op of kind BITVECTOR_ZERO_EXTEND
   *   -[2]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  BITVECTOR_ZERO_EXTEND,
  /**
   * Operator for bit-vector sign-extend.
   * Parameter 1:
   *   -[1]: Number of bits by which a given bit-vector is to be extended
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply bit-vector sign-extend.
   * Parameters: 2
   *   -[1]: Op of kind BITVECTOR_SIGN_EXTEND
   *   -[2]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  BITVECTOR_SIGN_EXTEND,
  /**
   * Operator for bit-vector rotate left.
   * Parameter 1:
   *   -[1]: Number of bits by which a given bit-vector is to be rotated
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply bit-vector rotate left.
   * Parameters: 2
   *   -[1]: Op of kind BITVECTOR_ROTATE_LEFT
   *   -[2]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  BITVECTOR_ROTATE_LEFT,
  /**
   * Operator for bit-vector rotate right.
   * Parameter 1:
   *   -[1]: Number of bits by which a given bit-vector is to be rotated
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply bit-vector rotate right.
   * Parameters: 2
   *   -[1]: Op of kind BITVECTOR_ROTATE_RIGHT
   *   -[2]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  BITVECTOR_ROTATE_RIGHT,
#if 0
  /* bit-vector boolean bit extract. */
  BITVECTOR_BITOF,
#endif
  /**
   * Operator for the conversion from Integer to bit-vector.
   * Parameter: 1
   *   -[1]: Size of the bit-vector to convert to
   * Create with:
   *   mkOp(Kind kind, uint32_t param).
   *
   * Apply integer conversion to bit-vector.
   * Parameters: 2
   *   -[1]: Op of kind INT_TO_BITVECTOR
   *   -[2]: Integer term
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  INT_TO_BITVECTOR,
  /**
   * Bit-vector conversion to (nonnegative) integer.
   * Parameter: 1
   *   -[1]: Term of bit-vector sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  BITVECTOR_TO_NAT,

  /* FP -------------------------------------------------------------------- */

  /**
   * Floating-point constant, constructed from a double or string.
   * Parameters: 3
   *   -[1]: Size of the exponent
   *   -[2]: Size of the significand
   *   -[3]: Value of the floating-point constant as a bit-vector term
   * Create with:
   *   mkFloatingPoint(uint32_t sig, uint32_t exp, Term val)
   */
  CONST_FLOATINGPOINT,
  /**
   * Floating-point rounding mode term.
   * Create with:
   *   mkRoundingMode(RoundingMode rm)
   */
  CONST_ROUNDINGMODE,
  /**
   * Create floating-point literal from bit-vector triple.
   * Parameters: 3
   *   -[1]: Sign bit as a bit-vector term
   *   -[2]: Exponent bits as a bit-vector term
   *   -[3]: Significand bits as a bit-vector term (without hidden bit)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_FP,
  /**
   * Floating-point equality.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_EQ,
  /**
   * Floating-point absolute value.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ABS,
  /**
   * Floating-point negation.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_NEG,
  /**
   * Floating-point addition.
   * Parameters: 3
   *   -[1]: CONST_ROUNDINGMODE
   *   -[2]: Term of sort FloatingPoint
   *   -[3]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_PLUS,
  /**
   * Floating-point sutraction.
   * Parameters: 3
   *   -[1]: CONST_ROUNDINGMODE
   *   -[2]: Term of sort FloatingPoint
   *   -[3]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_SUB,
  /**
   * Floating-point multiply.
   * Parameters: 3
   *   -[1]: CONST_ROUNDINGMODE
   *   -[2]: Term of sort FloatingPoint
   *   -[3]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_MULT,
  /**
   * Floating-point division.
   * Parameters: 3
   *   -[1]: CONST_ROUNDINGMODE
   *   -[2]: Term of sort FloatingPoint
   *   -[3]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_DIV,
  /**
   * Floating-point fused multiply and add.
   * Parameters: 4
   *   -[1]: CONST_ROUNDINGMODE
   *   -[2]: Term of sort FloatingPoint
   *   -[3]: Term of sort FloatingPoint
   *   -[4]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_FMA,
  /**
   * Floating-point square root.
   * Parameters: 2
   *   -[1]: CONST_ROUNDINGMODE
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_SQRT,
  /**
   * Floating-point remainder.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_REM,
  /**
   * Floating-point round to integral.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_RTI,
  /**
   * Floating-point minimum.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_MIN,
  /**
   * Floating-point maximum.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_MAX,
  /**
   * Floating-point less than or equal.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_LEQ,
  /**
   * Floating-point less than.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_LT,
  /**
   * Floating-point greater than or equal.
   * Parameters: 2
   *   -[1]..[2]: Terms of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_GEQ,
  /**
   * Floating-point greater than.
   * Parameters: 2
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FLOATINGPOINT_GT,
  /**
   * Floating-point is normal.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISN,
  /**
   * Floating-point is sub-normal.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISSN,
  /**
   * Floating-point is zero.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISZ,
  /**
   * Floating-point is infinite.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISINF,
  /**
   * Floating-point is NaN.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISNAN,
  /**
   * Floating-point is negative.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISNEG,
  /**
   * Floating-point is positive.
   * Parameters: 1
   *   -[1]: Term of floating point sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_ISPOS,
  /**
   * Operator for to_fp from bit vector.
   * Parameters: 2
   *   -[1]: Exponent size
   *   -[2]: Significand size
   * Create with:
   *   mkOp(Kind kind, uint32_t param1, uint32_t param2)
   *
   * Conversion from an IEEE-754 bit vector to floating-point.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_IEEE_BITVECTOR
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_IEEE_BITVECTOR,
  /**
   * Operator for to_fp from floating point.
   * Parameters: 2
   *   -[1]: Exponent size
   *   -[2]: Significand size
   * Create with:
   *   mkOp(Kind kind, uint32_t param1, uint32_t param2)
   *
   * Conversion between floating-point sorts.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_FLOATINGPOINT
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_FLOATINGPOINT,
  /**
   * Operator for to_fp from real.
   * Parameters: 2
   *   -[1]: Exponent size
   *   -[2]: Significand size
   * Create with:
   *   mkOp(Kind kind, uint32_t param1, uint32_t param2)
   *
   * Conversion from a real to floating-point.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_REAL
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_REAL,
  /*
   * Operator for to_fp from signed bit vector.
   * Parameters: 2
   *   -[1]: Exponent size
   *   -[2]: Significand size
   * Create with:
   *   mkOp(Kind kind, uint32_t param1, uint32_t param2)
   *
   * Conversion from a signed bit vector to floating-point.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR,
  /**
   * Operator for to_fp from unsigned bit vector.
   * Parameters: 2
   *   -[1]: Exponent size
   *   -[2]: Significand size
   * Create with:
   *   mkOp(Kind kind, uint32_t param1, uint32_t param2)
   *
   * Converting an unsigned bit vector to floating-point.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR,
  /**
   * Operator for a generic to_fp.
   * Parameters: 2
   *   -[1]: exponent size
   *   -[2]: Significand size
   * Create with:
   *   mkOp(Kind kind, uint32_t param1, uint32_t param2)
   *
   * Generic conversion to floating-point, used in parsing only.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_GENERIC
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_FP_GENERIC,
  /**
   * Operator for to_ubv.
   * Parameters: 1
   *   -[1]: Size of the bit-vector to convert to
   * Create with:
   *   mkOp(Kind kind, uint32_t param)
   *
   * Conversion from a floating-point value to an unsigned bit vector.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_TO_UBV
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_UBV,
  /**
   * Operator for to_sbv.
   * Parameters: 1
   *   -[1]: Size of the bit-vector to convert to
   * Create with:
   *   mkOp(Kind kind, uint32_t param)
   *
   * Conversion from a floating-point value to a signed bit vector.
   * Parameters: 2
   *   -[1]: Op of kind FLOATINGPOINT_TO_FP_TO_SBV
   *   -[2]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  FLOATINGPOINT_TO_SBV,
  /**
   * Floating-point to real.
   * Parameters: 1
   *   -[1]: Term of sort FloatingPoint
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  FLOATINGPOINT_TO_REAL,

  /* Arrays ---------------------------------------------------------------- */

  /**
   * Aarray select.
   * Parameters: 2
   *   -[1]: Term of array sort
   *   -[2]: Selection index
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  SELECT,
  /**
   * Array store.
   * Parameters: 3
   *   -[1]: Term of array sort
   *   -[2]: Store index
   *   -[3]: Term to store at the index
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2, Term child3)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  STORE,
  /**
   * Constant array.
   * Parameters: 2
   *   -[1]: Array sort
   *   -[2]: Term representing a constant
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2)
   *   mkTerm(Op op, const std::vector<Term>& children)
   *
   * Note: We currently support the creation of constant arrays, but under some
   * conditions when there is a chain of equalities connecting two constant
   * arrays, the solver doesn't know what to do and aborts (Issue #1667).
   */
  CONST_ARRAY,
  /**
   * Equality over arrays a and b over a given range [i,j], i.e.,
   * \forall k . i <= k <= j --> a[k] = b[k]
   *
   * Parameters: 4
   *   -[1]: First array
   *   -[2]: Second array
   *   -[3]: Lower bound of range (inclusive)
   *   -[4]: Uppper bound of range (inclusive)
   * Create with:
   *   mkTerm(Op op, const std::vector<Term>& children)
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
   * Paramters: n > 0
   *   -[1]: Constructor (operator)
   *   -[2]..[n]: Parameters to the constructor
   * Create with:
   *   mkTerm(Kind kind, Op op)
   *   mkTerm(Kind kind, Op op, Term child)
   *   mkTerm(Kind kind, Op op, Term child1, Term child2)
   *   mkTerm(Kind kind, Op op, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, Op op, const std::vector<Term>& children)
   */
  APPLY_CONSTRUCTOR,
  /**
   * Datatype selector application.
   * Parameters: 1
   *   -[1]: Selector (operator)
   *   -[2]: Datatype term (undefined if mis-applied)
   * Create with:
   *   mkTerm(Kind kind, Op op, Term child)
   */
  APPLY_SELECTOR,
  /**
   * Datatype tester application.
   * Parameters: 2
   *   -[1]: Tester term
   *   -[2]: Datatype term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
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
   * Parameters: 1
   *   -[1]: Index of the tuple to be updated
   * Create with:
   *   mkOp(Kind kind, uint32_t param)
   *
   * Apply tuple update.
   * Parameters: 3
   *   -[1]: Op of kind TUPLE_UPDATE (which references an index)
   *   -[2]: Tuple
   *   -[3]: Element to store in the tuple at the given index
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  TUPLE_UPDATE,
  /**
   * Operator for a record update.
   * Parameters: 1
   *   -[1]: Name of the field to be updated
   * Create with:
   *   mkOp(Kind kind, const std::string& param)
   *
   * Record update.
   * Parameters: 3
   *   -[1]: Op of kind RECORD_UPDATE (which references a field)
   *   -[2]: Record term to update
   *   -[3]: Element to store in the record in the given field
   * Create with:
   *   mkTerm(Op op, Term child1, Term child2)
   *   mkTerm(Op op,, const std::vector<Term>& children)
   */
  RECORD_UPDATE,
  /* Match expressions.
   * For example, the smt2 syntax match term
   *   (match l (((cons h t) h) (nil 0)))
   * is represented by the AST
   * (MATCH l
   *   (MATCH_BIND_CASE (BOUND_VAR_LIST h t) (cons h t) h)
   *   (MATCH_CASE nil 0))
   * The type of the last argument of each case term could be equal.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of kind MATCH_CASE or MATCH_BIND_CASE
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   *
   */
  MATCH,
  /* Match case
   * A (constant) case expression to be used within a match expression.
   * Parameters: 2
   *   -[1] Term denoting the pattern expression
   *   -[2] Term denoting the return value
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MATCH_CASE,
  /* Match bind case
   * A (non-constant) case expression to be used within a match expression.
   * Parameters: 3
   *   -[1] a BOUND_VAR_LIST Term containing the free variables of the case
   *   -[2] Term denoting the pattern expression
   *   -[3] Term denoting the return value
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MATCH_BIND_CASE,
  /*
   * Datatypes size
   * An operator mapping datatypes to an integer denoting the number of
   * non-nullary applications of constructors they contain.
   * Parameters: 1
   *   -[1]: Datatype term
   * Create with:
   *   mkTerm(Kind kind, Term child1)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  DT_SIZE,
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
   * Parameters: 0
   * Create with:
   *   mkSepNil(Sort sort)
   */
  SEP_NIL,
  /**
   * Separation logic empty heap.
   * Parameters: 2
   *   -[1]: Term of the same sort as the sort of the location of the heap
   *         that is constrained to be empty
   *   -[2]: Term of the same sort as the data sort of the heap that is
   *         that is constrained to be empty
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_EMP,
  /**
   * Separation logic points-to relation.
   * Parameters: 2
   *   -[1]: Location of the points-to constraint
   *   -[2]: Data of the points-to constraint
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_PTO,
  /**
   * Separation logic star.
   * Parameters: n >= 2
   *   -[1]..[n]: Child constraints that hold in disjoint (separated) heaps
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_STAR,
  /**
   * Separation logic magic wand.
   * Parameters: 2
   *   -[1]: Antecendant of the magic wand constraint
   *   -[2]: Conclusion of the magic wand constraint, which is asserted to
   *         hold in all heaps that are disjoint extensions of the antecedent.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEP_WAND,
#if 0
  /* separation label (internal use only) */
  SEP_LABEL,
#endif

  /* Sets ------------------------------------------------------------------ */

  /**
   * Empty set constant.
   * Parameters: 1
   *   -[1]: Sort of the set elements
   * Create with:
   *   mkEmptySet(Sort sort)
   */
  EMPTYSET,
  /**
   * Set union.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  UNION,
  /**
   * Set intersection.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INTERSECTION,
  /**
   * Set subtraction.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SETMINUS,
  /**
   * Subset predicate.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort, [1] a subset of set [2]?
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SUBSET,
  /**
   * Set membership predicate.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort, [1] a member of set [2]?
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  MEMBER,
  /**
   * The set of the single element given as a parameter.
   * Parameters: 1
   *   -[1]: Single element
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SINGLETON,
  /**
   * The set obtained by inserting elements;
   * Parameters: n > 0
   *   -[1]..[n-1]: Elements inserted into set [n]
   *   -[n]: Set Term
   * Create with:
   *   mkTerm(Kind kind, Term child)
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INSERT,
  /**
   * Set cardinality.
   * Parameters: 1
   *   -[1]: Set to determine the cardinality of
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  CARD,
  /**
   * Set complement with respect to finite universe.
   * Parameters: 1
   *   -[1]: Set to complement
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  COMPLEMENT,
  /**
   * Finite universe set.
   * All set variables must be interpreted as subsets of it.
   * Create with:
   *   mkUniverseSet(Sort sort)
   */
  UNIVERSE_SET,
  /**
   * Set join.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  JOIN,
  /**
   * Set cartesian product.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  PRODUCT,
  /**
   * Set transpose.
   * Parameters: 1
   *   -[1]: Term of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TRANSPOSE,
  /**
   * Set transitive closure.
   * Parameters: 1
   *   -[1]: Term of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  TCLOSURE,
  /**
   * Set join image.
   * Parameters: 2
   *   -[1]..[2]: Terms of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  JOIN_IMAGE,
  /**
   * Set identity.
   * Parameters: 1
   *   -[1]: Term of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  IDEN,
  /**
   * Set comprehension
   * A set comprehension is specified by a bound variable list x1 ... xn,
   * a predicate P[x1...xn], and a term t[x1...xn]. A comprehension C with the
   * above form has members given by the following semantics:
   * forall y. ( exists x1...xn. P[x1...xn] ^ t[x1...xn] = y ) <=> (member y C)
   * where y ranges over the element type of the (set) type of the
   * comprehension. If t[x1..xn] is not provided, it is equivalent to y in the
   * above formula.
   * Parameters: 2 (3)
   *   -[1]: Term BOUND_VAR_LIST
   *   -[2]: Term denoting the predicate of the comprehension
   *   -[3]: (optional) a Term denoting the generator for the comprehension
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  COMPREHENSION,
  /**
   * Returns an element from a given set.
   * If a set A = {x}, then the term (choose A) is equivalent to the term x.
   * If the set is empty, then (choose A) is an arbitrary value.
   * If the set has cardinality > 1, then (choose A) will deterministically
   * return an element in A.
   * Parameters: 1
   *   -[1]: Term of set sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  CHOOSE,

  /* Strings --------------------------------------------------------------- */

  /**
   * String concat.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_CONCAT,
  /**
   * String membership.
   * Parameters: 2
   *   -[1]: Term of String sort
   *   -[2]: Term of RegExp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_IN_REGEXP,
  /**
   * String length.
   * Parameters: 1
   *   -[1]: Term of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_LENGTH,
  /**
   * String substring.
   * Extracts a substring, starting at index i and of length l, from a string
   * s.  If the start index is negative, the start index is greater than the
   * length of the string, or the length is negative, the result is the empty
   * string.
   * Parameters: 3
   *   -[1]: Term of sort String
   *   -[2]: Term of sort Integer (index i)
   *   -[3]: Term of sort Integer (length l)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_SUBSTR,
  /**
   * String update.
   * Updates a string s by replacing its context starting at an index with t.
   * If the start index is negative, the start index is greater than the
   * length of the string, the result is s. Otherwise, the length of the
   * original string is preserved.
   * Parameters: 3
   *   -[1]: Term of sort String
   *   -[2]: Term of sort Integer (index i)
   *   -[3]: Term of sort String (replacement string t)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_UPDATE,
  /**
   * String character at.
   * Returns the character at index i from a string s. If the index is negative
   * or the index is greater than the length of the string, the result is the
   * empty string. Otherwise the result is a string of length 1.
   * Parameters: 2
   *   -[1]: Term of sort String (string s)
   *   -[2]: Term of sort Integer (index i)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_CHARAT,
  /**
   * String contains.
   * Checks whether a string s1 contains another string s2. If s2 is empty, the
   * result is always true.
   * Parameters: 2
   *   -[1]: Term of sort String (the string s1)
   *   -[2]: Term of sort String (the string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_CONTAINS,
  /**
   * String index-of.
   * Returns the index of a substring s2 in a string s1 starting at index i. If
   * the index is negative or greater than the length of string s1 or the
   * substring s2 does not appear in string s1 after index i, the result is -1.
   * Parameters: 3
   *   -[1]: Term of sort String (substring s1)
   *   -[2]: Term of sort String (substring s2)
   *   -[3]: Term of sort Integer (index i)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_INDEXOF,
  /**
   * String replace.
   * Replaces a string s2 in a string s1 with string s3. If s2 does not appear
   * in s1, s1 is returned unmodified.
   * Parameters: 3
   *   -[1]: Term of sort String (string s1)
   *   -[2]: Term of sort String (string s2)
   *   -[3]: Term of sort String (string s3)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_REPLACE,
  /**
   * String replace all.
   * Replaces all occurrences of a string s2 in a string s1 with string s3.
   * If s2 does not appear in s1, s1 is returned unmodified.
   * Parameters: 3
   *   -[1]: Term of sort String (string s1)
   *   -[2]: Term of sort String (string s2)
   *   -[3]: Term of sort String (string s3)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_REPLACE_ALL,
  /**
   * String replace regular expression match.
   * Replaces the first match of a regular expression r in string s1 with
   * string s2. If r does not match a substring of s1, s1 is returned
   * unmodified.
   * Parameters: 3
   *   -[1]: Term of sort String (string s1)
   *   -[2]: Term of sort Regexp (regexp r)
   *   -[3]: Term of sort String (string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_REPLACE_RE,
  /**
   * String replace all regular expression matches.
   * Replaces all matches of a regular expression r in string s1 with string
   * s2. If r does not match a substring of s1, s1 is returned unmodified.
   * Parameters: 3
   *   -[1]: Term of sort String (string s1)
   *   -[2]: Term of sort Regexp (regexp r)
   *   -[3]: Term of sort String (string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_REPLACE_RE_ALL,
  /**
   * String to lower case.
   * Parameters: 1
   *   -[1]: Term of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_TOLOWER,
  /**
   * String to upper case.
   * Parameters: 1
   *   -[1]: Term of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_TOUPPER,
  /**
   * String reverse.
   * Parameters: 1
   *   -[1]: Term of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_REV,
  /**
   * String to code.
   * Returns the code point of a string if it has length one, or returns -1
   * otherwise.
   * Parameters: 1
   *   -[1]: Term of String sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_TO_CODE,
  /**
   * String from code.
   * Returns a string containing a single character whose code point matches
   * the argument to this function, or the empty string if the argument is
   * out-of-bounds.
   * Parameters: 1
   *   -[1]: Term of Integer sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_FROM_CODE,
  /**
   * String less than.
   * Returns true if string s1 is (strictly) less than s2 based on a
   * lexiographic ordering over code points.
   * Parameters: 2
   *   -[1]: Term of sort String (the string s1)
   *   -[2]: Term of sort String (the string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_LT,
  /**
   * String less than or equal.
   * Returns true if string s1 is less than or equal to s2 based on a
   * lexiographic ordering over code points.
   * Parameters: 2
   *   -[1]: Term of sort String (the string s1)
   *   -[2]: Term of sort String (the string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_LEQ,
  /**
   * String prefix-of.
   * Checks whether a string s1 is a prefix of string s2. If string s1 is
   * empty, this operator returns true.
   * Parameters: 2
   *   -[1]: Term of sort String (string s1)
   *   -[2]: Term of sort String (string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_PREFIX,
  /**
   * String suffix-of.
   * Checks whether a string s1 is a suffix of string 2. If string s1 is empty,
   * this operator returns true.
   * Parameters: 2
   *   -[1]: Term of sort String (string s1)
   *   -[2]: Term of sort String (string s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_SUFFIX,
  /**
   * String is-digit.
   * Returns true if string s is digit (it is one of "0", ..., "9").
   * Parameters: 1
   *   -[1]: Term of sort String
   * Create with:
   *   mkTerm(Kind kind, Term child1)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  STRING_IS_DIGIT,
  /**
   * Integer to string.
   * If the integer is negative this operator returns the empty string.
   * Parameters: 1
   *   -[1]: Term of sort Integer
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_FROM_INT,
  /**
   * String to integer (total function).
   * If the string does not contain an integer or the integer is negative, the
   * operator returns -1.
   * Parameters: 1
   *   -[1]: Term of sort String
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_TO_INT,
  /**
   * Constant string.
   * Parameters:
   *   See mkString()
   * Create with:
   *   mkString(const char* s)
   *   mkString(const std::string& s)
   *   mkString(const unsigned char c)
   *   mkString(const std::vector<unsigned>& s)
   */
  CONST_STRING,
  /**
   * Conversion from string to regexp.
   * Parameters: 1
   *   -[1]: Term of sort String
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  STRING_TO_REGEXP,
  /**
   * Regexp Concatenation .
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_CONCAT,
  /**
   * Regexp union.
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_UNION,
  /**
   * Regexp intersection.
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_INTER,
  /**
   * Regexp difference.
   * Parameters: 2
   *   -[1]..[2]: Terms of Regexp sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_DIFF,
  /**
   * Regexp *.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  REGEXP_STAR,
  /**
   * Regexp +.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  REGEXP_PLUS,
  /**
   * Regexp ?.
   * Parameters: 1
   *   -[1]: Term of sort Regexp
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  REGEXP_OPT,
  /**
   * Regexp range.
   * Parameters: 2
   *   -[1]: Lower bound character for the range
   *   -[2]: Upper bound character for the range
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  REGEXP_RANGE,
  /**
   * Operator for regular expression repeat.
   * Parameters: 1
   *   -[1]: The number of repetitions
   * Create with:
   *   mkOp(Kind kind, uint32_t param)
   *
   * Apply regular expression loop.
   * Parameters: 2
   *   -[1]: Op of kind REGEXP_REPEAT
   *   -[2]: Term of regular expression sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  REGEXP_REPEAT,
  /**
   * Operator for regular expression loop, from lower bound to upper bound
   * number of repetitions.
   * Parameters: 2
   *   -[1]: The lower bound
   *   -[2]: The upper bound
   * Create with:
   *   mkOp(Kind kind, uint32_t param, uint32_t param)
   *
   * Apply regular expression loop.
   * Parameters: 2
   *   -[1]: Op of kind REGEXP_LOOP
   *   -[2]: Term of regular expression sort
   * Create with:
   *   mkTerm(Op op, Term child)
   *   mkTerm(Op op, const std::vector<Term>& children)
   */
  REGEXP_LOOP,
  /**
   * Regexp empty.
   * Parameters: 0
   * Create with:
   *   mkRegexpEmpty()
   *   mkTerm(Kind kind)
   */
  REGEXP_EMPTY,
  /**
   * Regexp all characters.
   * Parameters: 0
   * Create with:
   *   mkRegexpSigma()
   *   mkTerm(Kind kind)
   */
  REGEXP_SIGMA,
  /**
   * Regexp complement.
   * Parameters: 1
   *   -[1]: Term of sort RegExp
   * Create with:
   *   mkTerm(Kind kind, Term child1)
   */
  REGEXP_COMPLEMENT,

  /**
   * Sequence concat.
   * Parameters: n > 1
   *   -[1]..[n]: Terms of Sequence sort
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_CONCAT,
  /**
   * Sequence length.
   * Parameters: 1
   *   -[1]: Term of Sequence sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SEQ_LENGTH,
  /**
   * Sequence extract.
   * Extracts a subsequence, starting at index i and of length l, from a
   * sequence s.  If the start index is negative, the start index is greater
   * than the length of the sequence, or the length is negative, the result is
   * the empty sequence. Parameters: 3
   *   -[1]: Term of sort Sequence
   *   -[2]: Term of sort Integer (index i)
   *   -[3]: Term of sort Integer (length l)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_EXTRACT,
  /**
   * Sequence update.
   * Updates a sequence s by replacing its context starting at an index with t.
   * If the start index is negative, the start index is greater than the
   * length of the sequence, the result is s. Otherwise, the length of the
   * original sequence is preserved.
   * Parameters: 3
   *   -[1]: Term of sort Sequence
   *   -[2]: Term of sort Integer (index i)
   *   -[3]: Term of sort Sequence (replacement sequence t)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_UPDATE,
  /**
   * Sequence element at.
   * Returns the element at index i from a sequence s. If the index is negative
   * or the index is greater or equal to the length of the sequence, the result
   * is the empty sequence. Otherwise the result is a sequence of length 1.
   * Parameters: 2
   *   -[1]: Term of sequence sort (string s)
   *   -[2]: Term of sort Integer (index i)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_AT,
  /**
   * Sequence contains.
   * Checks whether a sequence s1 contains another sequence s2. If s2 is empty,
   * the result is always true. Parameters: 2
   *   -[1]: Term of sort Sequence (the sequence s1)
   *   -[2]: Term of sort Sequence (the sequence s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_CONTAINS,
  /**
   * Sequence index-of.
   * Returns the index of a subsequence s2 in a sequence s1 starting at index i.
   * If the index is negative or greater than the length of sequence s1 or the
   * subsequence s2 does not appear in sequence s1 after index i, the result is
   * -1. Parameters: 3
   *   -[1]: Term of sort Sequence (subsequence s1)
   *   -[2]: Term of sort Sequence (subsequence s2)
   *   -[3]: Term of sort Integer (index i)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_INDEXOF,
  /**
   * Sequence replace.
   * Replaces the first occurrence of a sequence s2 in a sequence s1 with
   * sequence s3. If s2 does not appear in s1, s1 is returned unmodified.
   * Parameters: 3
   *   -[1]: Term of sort Sequence (sequence s1)
   *   -[2]: Term of sort Sequence (sequence s2)
   *   -[3]: Term of sort Sequence (sequence s3)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_REPLACE,
  /**
   * Sequence replace all.
   * Replaces all occurrences of a sequence s2 in a sequence s1 with sequence
   * s3. If s2 does not appear in s1, s1 is returned unmodified. Parameters: 3
   *   -[1]: Term of sort Sequence (sequence s1)
   *   -[2]: Term of sort Sequence (sequence s2)
   *   -[3]: Term of sort Sequence (sequence s3)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_REPLACE_ALL,
  /**
   * Sequence reverse.
   * Parameters: 1
   *   -[1]: Term of Sequence sort
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  SEQ_REV,
  /**
   * Sequence prefix-of.
   * Checks whether a sequence s1 is a prefix of sequence s2. If sequence s1 is
   * empty, this operator returns true.
   * Parameters: 2
   *   -[1]: Term of sort Sequence (sequence s1)
   *   -[2]: Term of sort Sequence (sequence s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_PREFIX,
  /**
   * Sequence suffix-of.
   * Checks whether a sequence s1 is a suffix of sequence s2. If sequence s1 is
   * empty, this operator returns true. Parameters: 2
   *   -[1]: Term of sort Sequence (sequence s1)
   *   -[2]: Term of sort Sequence (sequence s2)
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  SEQ_SUFFIX,
  /**
   * Constant sequence.
   * Parameters:
   *   See mkEmptySequence()
   * Create with:
   *   mkEmptySequence(Sort sort)
   * Note that a constant sequence is a term that is equivalent to:
   *   (seq.++ (seq.unit c1) ... (seq.unit cn))
   * where n>=0 and c1, ..., cn are constants of some sort. The elements
   * can be extracted by Term::getConstSequenceElements().
   */
  CONST_SEQUENCE,
  /**
   * Sequence unit, corresponding to a sequence of length one with the given
   * term.
   * Parameters: 1
   *   -[1] Element term.
   * Create with:
   *   mkTerm(Kind kind, Term child1)
   */
  SEQ_UNIT,

  /* Quantifiers ----------------------------------------------------------- */

  /**
   * Universally quantified formula.
   * Parameters: 2 (3)
   *   -[1]: BOUND_VAR_LIST Term
   *   -[2]: Quantifier body
   *   -[3]: (optional) INST_PATTERN_LIST Term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  FORALL,
  /**
   * Existentially quantified formula.
   * Parameters: 2 (3)
   *   -[1]: BOUND_VAR_LIST Term
   *   -[2]: Quantifier body
   *   -[3]: (optional) INST_PATTERN_LIST Term
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  EXISTS,
  /*
   * A list of bound variables (used to bind variables under a quantifier)
   * Parameters: n > 1
   *   -[1]..[n]: Terms with kind BOUND_VARIABLE
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  BOUND_VAR_LIST,
  /*
   * A predicate for specifying term in instantiation closure.
   * Parameters: 1
   *   -[1]: Term
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  INST_CLOSURE,
  /*
   * An instantiation pattern.
   * Specifies a (list of) terms to be used as a pattern for quantifier
   * instantiation.
   * Parameters: n > 1
   *   -[1]..[n]: Terms with kind BOUND_VARIABLE
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INST_PATTERN,
  /*
   * An instantiation no-pattern.
   * Specifies a (list of) terms that should not be used as a pattern for
   * quantifier instantiation.
   * Parameters: n > 1
   *   -[1]..[n]: Terms with kind BOUND_VARIABLE
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
   */
  INST_NO_PATTERN,
  /*
   * An instantiation attribute
   * Specifies a custom property for a quantified formula given by a
   * term that is ascribed a user attribute.
   * Parameters: 1
   *   -[1]: Term with a user attribute.
   * Create with:
   *   mkTerm(Kind kind, Term child)
   */
  INST_ATTRIBUTE,
  /*
   * A list of instantiation patterns and/or attributes.
   * Parameters: n > 1
   *   -[1]..[n]: Terms with kind INST_PATTERN, INST_NO_PATTERN, or
   * INST_ATTRIBUTE.
   * Create with:
   *   mkTerm(Kind kind, Term child1, Term child2)
   *   mkTerm(Kind kind, Term child1, Term child2, Term child3)
   *   mkTerm(Kind kind, const std::vector<Term>& children)
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
  /* marks the upper-bound of this enumeration */
  LAST_KIND
};

/**
 * Get the string representation of a given kind.
 * @param k the kind
 * @return the string representation of kind k
 */
std::string kindToString(Kind k) CVC4_PUBLIC;

/**
 * Serialize a kind to given stream.
 * @param out the output stream
 * @param k the kind to be serialized to the given output stream
 * @return the output stream
 */
std::ostream& operator<<(std::ostream& out, Kind k) CVC4_PUBLIC;

/**
 * Hash function for Kinds.
 */
struct CVC4_PUBLIC KindHashFunction
{
  size_t operator()(Kind k) const;
};

}  // namespace api
}  // namespace CVC4

#endif
