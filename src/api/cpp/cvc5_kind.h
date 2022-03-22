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

// clang-format off
/**
 * The kind of a cvc5 Term.
 *
 * \internal
 *
 * Note that the API type `cvc5::api::Kind` roughly corresponds to
 * `cvc5::Kind`, but is a different type. It hides internal kinds that should
 * not be exported to the API, and maps all kinds that we want to export to its
 * corresponding internal kinds. The underlying type of `cvc5::api::Kind` must
 * be signed (to enable range checks for validity). The size of this type
 * depends on the size of `cvc5::Kind` (`NodeValue::NBITS_KIND`, currently 10
 * bits, see expr/node_value.h).
 */
enum Kind : int32_t
{
  /**
   * Internal kind.
   *
   * @note Should never be exposed or created via the API.
   */
  INTERNAL_KIND = -2,
  /**
   * Undefined kind.
   *
   * @note Should never be exposed or created via the API.
   */
  UNDEFINED_KIND = -1,
  /**
   * Null kind (kind of null term Term::Term()).
   *
   * @note May not be explicitly created via API functions other than
   *       Term::Term().
   */
  NULL_EXPR,

  /* Builtin --------------------------------------------------------------- */

  /**
   * The value of an uninterpreted constant.
   *
   * @note May be returned as the result of an API call, but terms of this kind
   *       may not be created explicitly via the API. Terms of this kind may
   *       further not appear in assertions.
   */
  UNINTERPRETED_SORT_VALUE,
#if 0
  /* Built-in operator */
  BUILTIN,
#endif
  /**
   * Equality, chainable.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of the same Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  EQUAL,
  /**
   * Disequality.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms with same sorts
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  DISTINCT,
  /**
   * First-order constant.
   *
   * @note Not permitted in bindings (e.g., #FORALL, #EXISTS).
   *
   * - Create Term of this Kind with:
   *   - Solver::mkConst(const Sort&, const std::string&) const
   *   - Solver::mkConst(const Sort&) const
   */
  CONSTANT,
  /**
   * (Bound) variable.
   *
   * @note Permitted in bindings and in the lambda and quantifier bodies only.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkVar(const Sort&, const std::string&) const
   */
  VARIABLE,
#if 0
  /* Skolem variable (internal only) */
  SKOLEM,
#endif
  /**
   * Symbolic expression.
   *
   * - Arity: `n > 0`
   *   - `1..n:` Terms with same sorts
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SEXPR,
  /**
   * Lambda expression.
   *
   * - Arity: `2`
   *   - `1:` Term of kind #VARIABLE_LIST
   *   - `2:` The body of the lambda, a Term of any Sort.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  LAMBDA,
  /**
   * The syntax of a witness term is similar to a quantified formula except that
   * only one variable is allowed.
   * The term `(witness ((x S)) F)` returns an element `x` of Sort `S`
   * and asserts `F`.
   *
   * The witness operator behaves like the description operator
   * (see https://planetmath.org/hilbertsvarepsilonoperator) if there is no
   * `x` that satisfies `F`. But if such `x` exists, the witness
   * operator does not enforce the axiom that ensures uniqueness up to logical
   * equivalence:
   *
   * @f[
   *   \forall x. F \equiv G \Rightarrow witness~x. F =  witness~x. G
   * @f]
   *
   * For example if there are 2 elements of Sort `S` that satisfy `F`,
   * then the following formula is satisfiable:
   *
   * \rst
   * .. code:: smtlib
   *
   *     (distinct
   *        (witness ((x Int)) F)
   *        (witness ((x Int)) F))
   * \endrst
   *
   * @note This kind is primarily used internally, but may be returned in
   *       models (e.g. for arithmetic terms in non-linear queries). However,
   *       it is not supported by the parser. Moreover, the user of the API
   *       should be cautious when using this operator. In general, all witness
   *       terms `(witness ((x Int)) F)` should be such that `(exists ((x Int))
   *       F)` is a valid formula. If this is not the case, then the semantics
   *       in formulas that use witness terms may be unintuitive. For example,
   *       the following formula is unsatisfiable:
   *       `(or (= (witness ((x Int)) false) 0) (not (= (witness ((x Int))
   *       false) 0))`, whereas notice that `(or (= z 0) (not (= z 0)))` is
   *       true for any `z`.
   *
   * - Arity: `2`
   *   - `1:` Term of kind #VARIABLE_LIST
   *   - `2:` The body of the lambda, a Term of any Sort.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  WITNESS,

  /* Boolean --------------------------------------------------------------- */

  /**
   * Boolean constant.
   *
   * - Create Term of this Kind with:
   *   - `Solver::mkTrue() const`
   *   - `Solver::mkFalse() const`
   *   - `Solver::mkBoolean(bool) const`
   */
  CONST_BOOLEAN,
  /**
   * Logical negation.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Bool
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  NOT,
  /**
   * Logical conjunction.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  AND,
  /**
   * Logical implication.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  IMPLIES,
  /**
   * Logical disjunction.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  OR,
  /**
   * Logical exclusive disjunction, left associative.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  XOR,
  /**
   * If-then-else.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort Bool
   *   - `2:` The 'then' term, Term of any Sort
   *   - `3:` The 'else' term, Term of the same sort as second argument
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ITE,

  /* UF -------------------------------------------------------------------- */

  /**
   * Application of an uninterpreted function.
   *
   * - Arity: `n > 1`
   *   - `1:` Function Term
   *   - `2..n:` Function argument instantiation Terms of any first-class Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  APPLY_UF,
#if 0
  /* Boolean term variable */
  BOOLEAN_TERM_VARIABLE,
#endif
  /**
   * Cardinality constraint on uninterpreted sort.
   *
   * Interpreted as a predicate that is true when the cardinality of
   * uinterpreted Sort `S` is less than or equal to the value of the second
   * argument.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort `S`
   *   - `2:` Positive integer constant that bounds the cardinality of `S`
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  CARDINALITY_CONSTRAINT,
  /**
   * Higher-order applicative encoding of function application, left
   * associative.
   *
   * - Arity: `n > 1`
   *   - `1:` Function Term
   *   - `2..n:` Function argument instantiation Terms of any Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  HO_APPLY,

  /* Arithmetic ------------------------------------------------------------ */

  /**
   * Arithmetic addition.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ADD,
  /**
   * Arithmetic multiplication.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  MULT,
  /**
   * Operator for bit-wise `AND` over integers, parameterized by a (positive)
   * bit-width `k`.
   *
   * `((_ iand k) i1 i2)` is equivalent to
   * `(bv2int (bvand ((_ int2bv k) i1) ((_ int2bv k) i2)))`
   * for all integers `i1`, `i2`.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort Int
   *   - `2:` Term of Sort Int
   *
   * - Indices: `1`
   *   - `1:` Bit-width `k`
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  IAND,
  /**
   * Operator for raising 2 to a non-negative integer power.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  POW2,
#if 0
  /* Synonym for MULT.  */
  NONLINEAR_MULT,
#endif
  /**
   * Arithmetic subtraction, left associative.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SUB,
  /**
   * Arithmetic negation.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  NEG,
  /**
   * Real division, division by 0 undefined, left associative.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  DIVISION,
  /**
   * Integer division, division by 0 undefined, left associative.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  INTS_DIVISION,
  /**
   * Integer modulus, division by 0 undefined.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort Int
   *   - `2:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  INTS_MODULUS,
  /**
   * Absolute value.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ABS,
  /**
   * Arithmetic power.
   *
   * - Arity: `2`
   *   - `1..2:` Term of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  POW,
  /**
   * Exponential function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  EXPONENTIAL,
  /**
   * Sine function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SINE,
  /**
   * Cosine function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  COSINE,
  /**
   * Tangent function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  TANGENT,
  /**
   * Cosecant function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  COSECANT,
  /**
   * Secant function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SECANT,
  /**
   * Cotangent function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  COTANGENT,
  /**
   * Arc sine function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ARCSINE,
  /**
   * Arc cosine function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ARCCOSINE,
  /**
   * Arc tangent function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ARCTANGENT,
  /**
   * Arc cosecant function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ARCCOSECANT,
  /**
   * Arc secant function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ARCSECANT,
  /**
   * Arc cotangent function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  ARCCOTANGENT,
  /**
   * Square root.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SQRT,
  /**
   * Operator for the divisibility-by-k predicate.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Indices: `1`
   *   - `1:` The integer `k` to divide by.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  DIVISIBLE,
  /**
   * Multiple-precision rational constant.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkInteger(const std::string&) const
   *   - Solver::mkInteger(int64_t) const
   *   - Solver::mkReal(const std::string&) const
   *   - Solver::mkReal(int64_t) const
   *   - Solver::mkReal(int64_t, int64_t) const
   */
  CONST_RATIONAL,
  /**
   * Less than, chainable.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  LT,
  /**
   * Less than or equal, chainable.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  LEQ,
  /**
   * Greater than, chainable.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  GT,
  /**
   * Greater than or equal, chainable.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  GEQ,
  /**
   * Is-integer predicate.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  IS_INTEGER,
  /**
   * Convert Term of sort Int or Real to Int via the floor function.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  TO_INTEGER,
  /**
   * Convert Term of Sort Int or Real to Real.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  TO_REAL,
  /**
   * Pi constant.
   *
   * @note #PI is considered a special symbol of Sort Real, but is not
   * a Real value, i.e., `Term::isRealValue() const` will return `false`.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkPi() const
   */
  PI,

  /* BV -------------------------------------------------------------------- */

  /**
   * Fixed-size bit-vector constant.
   *
   * - Create Term of this Kind with:
   *   - `Solver::mkBitVector(uint32_t, uint64_t) const`
   *   - `Solver::mkBitVector(uint32_t, const std::string&, uint32_t) const`
   */
  CONST_BITVECTOR,
  /**
   * Concatenation of two or more bit-vectors.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_CONCAT,
  /**
   * Bit-wise and.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_AND,
  /**
   * Bit-wise or.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_OR,
  /**
   * Bit-wise xor.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_XOR,
  /**
   * Bit-wise negation.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_NOT,
  /**
   * Bit-wise nand.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_NAND,
  /**
   * Bit-wise nor.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_NOR,
  /**
   * Bit-wise xnor, left associative.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_XNOR,
  /**
   * Equality comparison (returns bit-vector of size 1).
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_COMP,
  /**
   * Multiplication of two or more bit-vectors.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_MULT,
  /**
   * Addition of two or more bit-vectors.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_ADD,
  /**
   * Subtraction of two bit-vectors.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SUB,
  /**
   * Negation of a bit-vector (two's complement).
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_NEG,
  /**
   * Unsigned bit-vector division.
   *
   * Truncates towards 0. If the divisor is zero, the result is all ones.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_UDIV,
  /**
   * Unsigned bit-vector remainder.
   *
   * Remainder from unsigned bit-vector division. If the modulus is zero, the
   * result is the dividend.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_UREM,
  /**
   * Signed bit-vector division.
   *
   * Two's complement signed division of two bit-vectors. If the divisor is
   * zero and the dividend is positive, the result is all ones. If the divisor
   * is zero and the dividend is negative, the result is one.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SDIV,
  /**
   * Signed bit-vector remainder (sign follows dividend).
   *
   * Two's complement signed remainder of two bit-vectors where the sign
   * follows the dividend. If the modulus is zero, the result is the dividend.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SREM,
  /**
   * Signed bit-vector remainder (sign follows divisor).
   *
   * Two's complement signed remainder where the sign follows the divisor. If
   * the modulus is zero, the result is the dividend.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SMOD,
  /**
   * Bit-vector shift left.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SHL,
  /**
   * Bit-vector logical shift right.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_LSHR,
  /**
   * Bit-vector arithmetic shift right.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_ASHR,
  /**
   * Bit-vector unsigned less than.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_ULT,
  /**
   * Bit-vector unsigned less than or equal.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_ULE,
  /**
   * Bit-vector unsigned greater than.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_UGT,
  /**
   * Bit-vector unsigned greater than or equal.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_UGE,
  /**
   * Bit-vector signed less than.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SLT,
  /**
   * Bit-vector signed less than or equal.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SLE,
  /**
   * Bit-vector signed greater than.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SGT,
  /**
   * Bit-vector signed greater than or equal.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SGE,
  /**
   * Bit-vector unsigned less than returning a bit-vector of size 1.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_ULTBV,
  /**
   * Bit-vector signed less than returning a bit-vector of size 1.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_SLTBV,
  /**
   * Bit-vector if-then-else.
   *
   * Same semantics as regular ITE, but condition is bit-vector of size 1.
   *
   * - Arity: `3`
   *   - `1:` Term of bit-vector Sort of size `1`
   *   - `1..3:` Terms of bit-vector sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_ITE,
  /**
   * Bit-vector redor.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_REDOR,
  /**
   * Bit-vector redand.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
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
   * Bit-vector extract.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `2`
   *   - `1:` The upper bit index.
   *   - `2:` The lower bit index.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t, uint32_t) const
   */
  BITVECTOR_EXTRACT,
  /**
   * Bit-vector repeat.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `1`
   *   - `1:` The number of times to repeat the given term.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  BITVECTOR_REPEAT,
  /**
   * Bit-vector zero extension.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `1`
   *   - `1:` The number of zeroes to extend the given term with.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  BITVECTOR_ZERO_EXTEND,
  /**
   * Bit-vector sign extension.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `1`
   *   - `1:` The number of bits (of the value of the sign bit) to extend
   *          the given term with.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  BITVECTOR_SIGN_EXTEND,
  /**
   * Bit-vector rotate left.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `1`
   *   - `1:` The number of bits to rotate the given term left.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  BITVECTOR_ROTATE_LEFT,
  /**
   * Bit-vector rotate right.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `1`
   *   - `1:` The number of bits to rotate the given term right.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  BITVECTOR_ROTATE_RIGHT,
#if 0
  /* bit-vector boolean bit extract. */
  BITVECTOR_BITOF,
#endif
  /**
   * Conversion from Int to bit-vector.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Indices: `1`
   *   - `1:` The size of the bit-vector to convert to.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  INT_TO_BITVECTOR,
  /**
   * Bit-vector conversion to (non-negative) integer.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  BITVECTOR_TO_NAT,

  /* FP -------------------------------------------------------------------- */

  /**
   * Floating-point constant, created from IEEE-754 bit-vector representation
   * of the floating-point value.
   *
   * - Create Term of this Kind with:
   *   - Term mkFloatingPoint(uint32_t, uint32_t, Term) const;
   */
  CONST_FLOATINGPOINT,
  /**
   * RoundingMode constant.
   *
   * - Create Term of this Kind with:
   *   - `Solver::mkRoundingMode(RoundingMode rm) const`
   */
  CONST_ROUNDINGMODE,
  /**
   * Create floating-point literal from bit-vector triple.
   *
   * - Arity: `3`
   *   - `1:` Term of bit-vector Sort of size `1` (sign bit)
   *   - `2:` Term of bit-vector Sort of exponent size (exponent)
   *   - `3:` Term of bit-vector Sort of significand size - 1
   *          (significand without hidden bit)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_FP,
  /**
   * Floating-point equality.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_EQ,
  /**
   * Floating-point absolute value.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_ABS,
  /**
   * Floating-point negation.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_NEG,
  /**
   * Floating-point addition.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort RoundingMode
   *   - `2..3:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_ADD,
  /**
   * Floating-point sutraction.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort RoundingMode
   *   - `2..3:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_SUB,
  /**
   * Floating-point multiply.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort RoundingMode
   *   - `2..3:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_MULT,
  /**
   * Floating-point division.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort RoundingMode
   *   - `2..3:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_DIV,
  /**
   * Floating-point fused multiply and add.
   *
   * - Arity: `4`
   *   - `1:` Term of Sort RoundingMode
   *   - `2..4:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_FMA,
  /**
   * Floating-point square root.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort RoundingMode
   *   - `2:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_SQRT,
  /**
   * Floating-point remainder.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_REM,
  /**
   * Floating-point round to integral.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_RTI,
  /**
   * Floating-point minimum.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_MIN,
  /**
   * Floating-point maximum.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_MAX,
  /**
   * Floating-point less than or equal.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_LEQ,
  /**
   * Floating-point less than.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_LT,
  /**
   * Floating-point greater than or equal.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_GEQ,
  /**
   * Floating-point greater than.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_GT,
  /**
   * Floating-point is normal tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_NORMAL,
  /**
   * Floating-point is sub-normal tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_SUBNORMAL,
  /**
   * Floating-point is zero tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_ZERO,
  /**
   * Floating-point is infinite tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_INF,
  /**
   * Floating-point is NaN tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_NAN,
  /**
   * Floating-point is negative tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_NEG,
  /**
   * Floating-point is positive tester.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_IS_POS,
  /**
   * Conversion to floating-point from IEEE-754 bit-vector.
   *
   * - Arity: `1`
   *   - `1:` Term of bit-vector Sort
   *
   * - Indices: `2`
   *   - `1:` The exponent size
   *   - `2:` The significand size
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t, uint32_t) const
   */
  FLOATINGPOINT_TO_FP_FROM_IEEE_BV,
  /**
   * Conversion to floating-point from floating-point.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort RoundingMode
   *   - `2:` Term of floating-point Sort
   *
   * - Indices: `2`
   *   - `1:` The exponent size
   *   - `2:` The significand size
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t, uint32_t) const
   */
  FLOATINGPOINT_TO_FP_FROM_FP,
  /**
   * Conversion to floating-point from Real.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort RoundingMode
   *   - `2:` Term of Sort Real
   *
   * - Indices: `2`
   *   - `1:` The exponent size
   *   - `2:` The significand size
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t, uint32_t) const
   */
  FLOATINGPOINT_TO_FP_FROM_REAL,
  /**
   * Conversion to floating-point from signed bit-vector.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort RoundingMode
   *   - `2:` Term of bit-vector Sort
   *
   * - Indices: `2`
   *   - `1:` The exponent size
   *   - `2:` The significand size
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t, uint32_t) const
   */
  FLOATINGPOINT_TO_FP_FROM_SBV,
  /**
   * Conversion to floating-point from unsigned bit-vector.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort RoundingMode
   *   - `2:` Term of bit-vector Sort
   *
   * - Indices: `2`
   *   - `1:` The exponent size
   *   - `2:` The significand size
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t, uint32_t) const
   */
  FLOATINGPOINT_TO_FP_FROM_UBV,
  /**
   * Conversion to unsigned bit-vector from floating-point.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Indices: `1`
   *   - `1:` The size of the bit-vector to convert to.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  FLOATINGPOINT_TO_UBV,
  /**
   * Conversion to signed bit-vector from floating-point.
   *
   * - Arity: `1`
   *   - `1:` Term of floating-point Sort
   *
   * - Indices: `1`
   *   - `1:` The size of the bit-vector to convert to.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, uint32_t) const
   */
  FLOATINGPOINT_TO_SBV,
  /**
   * Conversion to Real from floating-point.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  FLOATINGPOINT_TO_REAL,

  /* Arrays ---------------------------------------------------------------- */

  /**
   * Array select.
   *
   * - Arity: `2`
   *   - `1:` Term of array Sort
   *   - `2:` Term of array index Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SELECT,
  /**
   * Array store.
   *
   * - Arity: `3`
   *   - `1:` Term of array Sort
   *   - `2:` Term of array index Sort
   *   - `3:` Term of array element Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  STORE,
  /**
   * Constant array.
   *
   * - Arity: `2`
   *   - `1:` Term of array Sort
   *   - `2:` Term of array element Sort (value)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  CONST_ARRAY,
  /**
   * Equality over arrays `a` and `b` over a given range `[i,j]`, i.e.,
   * @f[
   *   \forall k . i \leq k \leq j \Rightarrow a[k] = b[k]
   * @f]
   *
   * @note We currently support the creation of array equalities over index
   *       types bit-vector, floating-point, integer and real.
   *       \verbatim embed:rst:leading-asterisk
   *       Requires to enable option :ref:`arrays-exp<lbl-option-arrays-exp>`.
   *       \endverbatim
   *
   * - Arity: `4`
   *   - `1:` Term of array Sort (first array)
   *   - `2:` Term of array Sort (second array)
   *   - `3:` Term of array index Sort (lower bound of range, inclusive)
   *   - `4:` Term of array index Sort (upper bound of range, inclusive)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   *
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
   * Datatype constructor application.
   *
   * - Arity: `n > 0`
   *   - `1:` DatatypeConstructor Term
   *          (see DatatypeConstructor::getConstructorTerm() const,
   *          Datatype::getConstructorTerm(const std::string&) const)
   *   - `2..n:` Terms of the Sorts of the selectors of the constructor (the arguments to the constructor)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  APPLY_CONSTRUCTOR,
  /**
   * Datatype selector application.
   *
   * @note Undefined if misapplied.
   *
   * - Arity: `2`
   *   - `1:` DatatypeSelector Term
   *          (see DatatypeSelector::getSelectorTerm() const,
   *          DatatypeConstructor::getSelectorTerm(const std::string&) const)
   *   - `2:` Term of the codomain Sort of the selector
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  APPLY_SELECTOR,
  /**
   * Datatype tester application.
   *
   * - Arity: `2`
   *   - `1:` Datatype tester Term
   *          (see DatatypeConstructor::getTesterTerm() const)
   *   - `2:` Term of Datatype Sort (DatatypeConstructor must belong to this
   *          Datatype Sort)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  APPLY_TESTER,
  /**
   * Datatype update application.
   *
   * @note Does not change the datatype argument if misapplied.
   *
   * - Arity: `3`
   *   - `1:` Datatype updater Term
   *          (see DatatypeSelector::getUpdaterTerm() const)
   *   - `2:` Term of Datatype Sort (DatatypeSelector must belong to a
   *          constructor of this Datatype Sort)
   *   - `3:` Term of the codomain Sort of the selector (the Term to update
   *          the field of the datatype term with)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  APPLY_UPDATER,
  /**
   * Match expression.
   *
   * For example, the SMT-LIBv2 syntax for the following match term
   * \rst
   * .. code:: smtlib
   *
   *      (match l (((cons h t) h) (nil 0)))
   * \endrst
   * is represented by the AST
   *
   * \rst
   * .. code:: lisp
   *
   *     (MATCH l
   *         (MATCH_BIND_CASE (VARIABLE_LIST h t) (cons h t) h)
   *         (MATCH_CASE nil 0))
   * \endrst
   *
   * Terms of kind #MATCH_CASE are constant case expressions, which are used
   * for nullary constructors. Kind #MATCH_BIND_CASE is used for constructors
   * with selectors and variable match patterns. If not all constructors are
   * covered, at least one catch-all variable pattern must be included.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of kind #MATCH_CASE and #MATCH_BIND_CASE
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  MATCH,
  /**
   * Match case for nullary constructors.
   *
   * A (constant) case expression to be used within a match expression.
   *
   * - Arity: `2`
   *   - `1:` Term of kind #APPLY_CONSTRUCTOR
   *   - `2:` Term of any Sort (the term to match against)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  MATCH_CASE,
  /**
   * Match case with binders, for constructors with selectors and variable
   * patterns.
   *
   * A (non-constant) case expression to be used within a match expression.
   *
   * - Arity: `3`
   *   - For variable patterns:
   *     - `1:` Term of kind #VARIABLE_LIST (containing the free variable of
   *            the case)
   *     - `2:` Term of kind #VARIABLE (the pattern expression, the free
   *            variable of the case)
   *     - `3:` Term of any Sort (the term to match against)
   *   - For constructors with selectors:
   *     - `1:` Term of kind #VARIABLE_LIST (containing the free variable of
   *            the case)
   *     - `2:` Term of kind #APPLY_CONSTRUCTOR (the pattern expression,
   *            applying the set of variables to the constructor)
   *     - `3:` Term of any Sort (the term to match against)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  MATCH_BIND_CASE,
  /**
   * Datatypes size operator.
   *
   * An operator mapping a datatype term to an integer denoting the number of
   * non-nullary applications of constructors it contains.
   *
   * - Arity: `1`
   *   - `1:` Term of datatype Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  DT_SIZE,
  /**
   * Tuple projection.
   *
   * This operator takes a tuple as an argument and returns a tuple obtained by
   * concatenating components of its argument at the provided indices.
   *
   * For example,
   * \rst
   * .. code:: smtlib
   *
   *     ((_ tuple_project 1 2 2 3 1) (tuple 10 20 30 40))
   * \endrst
   * yields
   * \rst
   * .. code:: smtlib
   *
   *     (tuple 20 30 30 40 20)
   * \endrst
   *
   * - Arity: `1`
   *   - `1:` Term of tuple Sort
   *
   * - Indices: `n`
   *   - `1..n:` The tuple indices to project
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   * Separation logic nil.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkSepNil(const Sort&) const
   */
  SEP_NIL,
  /**
   * Separation logic empty heap.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkSepEmp() const
   */
  SEP_EMP,
  /**
   * Separation logic points-to relation.
   *
   * - Arity: `2`
   *   - `1:` Term denoting the location of the points-to constraint
   *   - `2:` Term denoting the data of the points-to constraint
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SEP_PTO,
  /**
   * Separation logic star.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of sort Bool (the child constraints that hold in
   *             disjoint (separated) heaps)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SEP_STAR,
  /**
   * Separation logic magic wand.
   *
   * - Arity: `2`
   *   - `1:` Terms of Sort Bool (the antecendant of the magic wand constraint)
   *   - `2:` Terms of Sort Bool (conclusion of the magic wand constraint,
   *          which is asserted to hold in all heaps that are disjoint
   *          extensions of the antecedent)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SEP_WAND,
#if 0
  /* separation label (internal use only) */
  SEP_LABEL,
#endif

  /* Sets ------------------------------------------------------------------ */

  /**
   * Empty set.
   *
   * - Create Term of this Kind with:
   *   - `Solver::mkEmptySet(const Sort&) const`
   */
  SET_EMPTY,
  /**
   * Set union.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_UNION,
  /**
   * Set intersection.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_INTER,
  /**
   * Set subtraction.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_MINUS,
  /**
   * Subset predicate.
   *
   * Determines if the first set is a subset of the second set.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_SUBSET,
  /**
   * Set membership predicate.
   *
   * Determines if the given set element is a member of the second set.
   *
   * - Arity: `2`
   *   - `1:` Term of any Sort (must match the element sort of the
   *          given set Term)
   *   - `2:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_MEMBER,
  /**
   * Singleton set.
   *
   * Construct a singleton set from an element given as a parameter.
   * The returned set has same type of the element.
   *
   * - Arity: `1`
   *   - `1:` Term of any Sort (the set element)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_SINGLETON,
  /**
   * The set obtained by inserting elements;
   *
   * - Arity: `n > 0`
   *   - `1..n-1:` Terms of any Sort (must match the element sort of the
   *               given set Term)
   *   - `n:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_INSERT,
  /**
   * Set cardinality.
   *
   * - Arity: `1`
   *   - `1:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_CARD,
  /**
   * Set complement with respect to finite universe.
   *
   * - Arity: `1`
   *   - `1:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_COMPLEMENT,
  /**
   * Finite universe set.
   *
   * All set variables must be interpreted as subsets of it.
   *
   * @note #SET_UNIVERSE is considered a special symbol of the theory of
   *       sets and is not considered as a set value, i.e.,
   *       Term::isSetValue() const will return `false`.
   *
   * - Create Op of this kind with:
   *   - Solver::mkUniverseSet(const Sort&) const
   */
  SET_UNIVERSE,
  /**
   * Set comprehension
   *
   * A set comprehension is specified by a variable list @f$x_1 ... x_n@f$,
   * a predicate @f$P[x_1...x_n]@f$, and a term @f$t[x_1...x_n]@f$. A
   * comprehension @f$C@f$ with the above form has members given by the
   * following semantics:
   * @f[
   *  \forall y. ( \exists x_1...x_n. P[x_1...x_n] \hat{} t[x_1...x_n] = y )
   * \Leftrightarrow (member y C)
   * @f]
   * where @f$y@f$ ranges over the element type of the (set) type of the
   * comprehension. If @f$t[x_1..x_n]@f$ is not provided, it is equivalent to
   * @f$y@f$ in the above formula.
   *
   * - Arity: `3`
   *   - `1:` Term of Kind #VARIABLE_LIST
   *   - `2:` Term of sort Bool (the predicate of the comprehension)
   *   - `3:` (optional) Term denoting the generator for the comprehension
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_COMPREHENSION,
  /**
   * Select an element from a given set.
   *
   * For a set `A = {x}`, the term `(set.choose A)` is equivalent to the term
   * `x`. For an empty set, it is an arbitrary value. For a set with
   * cardinality > 1, then it will deterministically return an element in `A`.
   *
   * - Arity: `1`
   *   - `1:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_CHOOSE,
  /**
   * Set is singleton tester.
   *
   * - Arity: `1`
   *   - `1:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
  SET_IS_SINGLETON,
  /**
   * Set map.
   *
   * This operator applies the first argument, a function of Sort
   * `(-> S_1 S_2)`, to every element of the second argument, a set of type
   * `(Set S_1)`, and returns a set of Sort `(Set S_2)`.
   *
   * - Arity: `1`
   *   - `1:` Term of function Sort `(-> S_1 S_2)`
   *   - `2:` Term of set Sort `(Set S_1)`
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind) const
   */
   SET_MAP,

  /* Relations ------------------------------------------------------------- */

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
  RELATION_JOIN,
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
  RELATION_PRODUCT,
  /**
   * Set transpose.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  RELATION_TRANSPOSE,
  /**
   * Set transitive closure.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  RELATION_TCLOSURE,
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
  RELATION_JOIN_IMAGE,
  /**
   * Set identity.
   *
   * Parameters:
   *   - 1: Term of set sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child) const`
   */
  RELATION_IDEN,

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
  BAG_EMPTY,
  /**
   * Bag max union.
   *
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BAG_UNION_MAX,
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
  BAG_UNION_DISJOINT,
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
  BAG_INTER_MIN,
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
  BAG_DIFFERENCE_SUBTRACT,
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
  BAG_DIFFERENCE_REMOVE,
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
  BAG_SUBBAG,
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
   * Bag membership predicate.
   *
   * Parameters:
   *   - 1..2: Terms of bag sort (Bag E), is [1] of type E an element of [2]
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BAG_MEMBER,
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
  BAG_DUPLICATE_REMOVAL,
  /**
   * Construct a bag with the given element and given multiplicity.
   *
   * Parameters:
   *   - 1: The element
   *   - 2: The multiplicity of the element. 
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child, const Term& child) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BAG_MAKE,
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
   *
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
  /**
   * bag.map operator applies the first argument, a function of type (-> T1 T2),
   * to every element of the second argument, a bag of type (Bag T1),
   * and returns a bag of type (Bag T2).
   *
   * Parameters:
   *   - 1: a function of type (-> T1 T2)
   *   - 2: a bag of type (Bag T1)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BAG_MAP,
  /**
    * bag.filter operator filters the elements of a bag.
    * (bag.filter p B) takes a predicate p of type (-> T Bool) as a first
    * argument, and a bag B of type (Bag T) as a second argument, and returns a
    * subbag of type (Bag T) that includes all elements of B that satisfy p
    * with the same multiplicity.
    *
    * Parameters:
    *   - 1: a function of type (-> T Bool)
    *   - 2: a bag of type (Bag T)
    *
    * Create with:
    *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
    *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
    */
   BAG_FILTER,
  /**
   * bag.fold operator combines elements of a bag into a single value.
   * (bag.fold f t B) folds the elements of bag B starting with term t and using
   * the combining function f.
   *
   * Parameters:
   *   - 1: a binary operation of type (-> T1 T2 T2)
   *   - 2: an initial value of type T2
   *   - 2: a bag of type (Bag T1)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  BAG_FOLD,
  /**
   * Table cross product.
   *
   * Parameters:
   *   - 1..2: Terms of bag sort
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  TABLE_PRODUCT,

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
   * String index-of regular expression match.
   * Returns the first match of a regular expression r in a string s. If the
   * index is negative or greater than the length of string s1, or r does not
   * match a substring in s after index i, the result is -1.
   *
   * Parameters:
   *   - 1: Term of sort String (string s)
   *   - 2: Term of sort RegLan (regular expression r)
   *   - 3: Term of sort Integer (index i)
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  STRING_INDEXOF_RE,
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
   * Regexp \*.
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
   * Regexp none.
   *
   * Parameters: none
   *
   * Create with:
   *   - `Solver::mkRegexpNone() const`
   *   - `Solver::mkTerm(Kind kind) const`
   */
  REGEXP_NONE,
  /**
   * Regexp all.
   *
   * Parameters: none
   *
   * Create with:
   *   - `Solver::mkRegexpAll() const`
   *   - `Solver::mkTerm(Kind kind) const`
   */
  REGEXP_ALL,
  /**
   * Regexp all characters.
   *
   * Parameters: none
   *
   * Create with:
   *   - `Solver::mkRegexpAllchar() const`
   *   - `Solver::mkTerm(Kind kind) const`
   */
  REGEXP_ALLCHAR,
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
   * can be extracted by `Term::getSequenceValue()`.
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
   *   - 1: VARIABLE_LIST Term
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
   *   - 1: VARIABLE_LIST Term
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
   * A list of variables (used to bind variables under a quantifier)
   *
   * Parameters: n > 1
   *   - 1..n: Terms with kind VARIABLE
   *
   * Create with:
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const`
   *   - `Solver::mkTerm(Kind kind, const Term& child1, const Term& child2, const Term& child3) const`
   *   - `Solver::mkTerm(Kind kind, const std::vector<Term>& children) const`
   */
  VARIABLE_LIST,
  /**
   * An instantiation pattern.
   * Specifies a (list of) terms to be used as a pattern for quantifier
   * instantiation.
   *
   * Parameters: n > 1
   *   - 1..n: Terms of any sort
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
   *   - 1..n: Terms of any sort
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
   *
   * Parameters: n > 1
   *   - 1..n: Terms that comprise the pools, which are one-to-one with the variables of the quantified formula to be instantiated.
   *
   * Create with:
   *   - `mkTerm(Kind kind, Term child1, Term child2)`
   *   - `mkTerm(Kind kind, Term child1, Term child2, Term child3)`
   *   - `mkTerm(Kind kind, const std::vector<Term>& children)`
   */
  INST_POOL,
  /*
   * A instantantiation-add-to-pool annotation.
   *
   * Parameters: n = 1
   *   - 1: The pool to add to.
   *
   * Create with:
   *   - `mkTerm(Kind kind, Term child)`
   */
  INST_ADD_TO_POOL,
  /*
   * A skolemization-add-to-pool annotation.
   *
   * Parameters: n = 1
   *   - 1: The pool to add to.
   *
   * Create with:
   *   - `mkTerm(Kind kind, Term child)`
   */
  SKOLEM_ADD_TO_POOL,
  /**
   * An instantiation attribute
   * Specifies a custom property for a quantified formula given by a
   * term that is ascribed a user attribute.
   *
   * Parameters: n >= 1
   *   - 1: The keyword of the attribute (a term with kind CONST_STRING).
   *   - 2...n: The values of the attribute.
   *
   * Create with:
   *   - `mkTerm(Kind kind, Term child1, Term child2)`
   *   - `mkTerm(Kind kind, Term child1, Term child2, Term child3)`
   *   - `mkTerm(Kind kind, const std::vector<Term>& children)`
   */
  INST_ATTRIBUTE,
  /**
   * A list of instantiation patterns and/or attributes.
   *
   * Parameters: n > 1
   *   - 1..n: Terms with kind INST_PATTERN, INST_NO_PATTERN, or INST_ATTRIBUTE.
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
// clang-format on

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
