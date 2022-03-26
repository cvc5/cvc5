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

namespace cvc5::api {

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
   * This kind serves as an abstraction for internal kinds that are not exposed
   * via the API but may appear in terms returned by API functions, e.g.,
   * when querying the simplified form of a term.
   *
   * @note Should never be created via the API.
   */
  INTERNAL_KIND = -2,
  /**
   * Undefined kind.
   *
   * @note Should never be exposed or created via the API.
   */
  UNDEFINED_KIND = -1,
  /**
   * Null kind.
   *
   * The kind of a null term (Term::Term()).
   *
   * @note May not be explicitly created via API functions other than
   *       Term::Term().
   */
  NULL_TERM,

  /* Builtin --------------------------------------------------------------- */

  /**
   * The value of an uninterpreted constant.
   *
   * @note May be returned as the result of an API call, but terms of this kind
   *       may not be created explicitly via the API and may not appear in
   *       assertions.
   */
  UNINTERPRETED_SORT_VALUE,
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EQUAL,
  /**
   * Disequality.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of the same Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  DISTINCT,
  /**
   * Free constant symbol.
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
   * @note Only permitted in bindings and in lambda and quantifier bodies.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkVar(const Sort&, const std::string&) const
   */
  VARIABLE,
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEXPR,
  /**
   * Lambda expression.
   *
   * - Arity: `2`
   *   - `1:` Term of kind #VARIABLE_LIST
   *   - `2:` Term of any Sort (the body of the lambda)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  LAMBDA,
  /**
   * Witness.
   *
   * The syntax of a witness term is similar to a quantified formula except that
   * only one variable is allowed.
   * For example, the term
   * \rst
   * .. code:: smtlib
   *
   *     (witness ((x S)) F)
   * \endrst
   * returns an element @f$x@f$ of Sort @f$S@f$ and asserts formula @f$F@f$.
   *
   * The witness operator behaves like the description operator
   * (see https://planetmath.org/hilbertsvarepsilonoperator) if there is
   * no @f$x@f$ that satisfies @f$F@f$. But if such @f$x@f$ exists, the witness
   * operator does not enforce the following axiom which ensures uniqueness up
   * to logical equivalence:
   *
   * @f[
   *   \forall x. F \equiv G \Rightarrow witness~x. F =  witness~x. G
   * @f]
   *
   * For example, if there are two elements of Sort @f$S@f$ that satisfy
   * formula @f$F@f$, then the following formula is satisfiable:
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
   *       models (e.g., for arithmetic terms in non-linear queries). However,
   *       it is not supported by the parser. Moreover, the user of the API
   *       should be cautious when using this operator. In general, all witness
   *       terms `(witness ((x Int)) F)` should be such that `(exists ((x Int))
   *       F)` is a valid formula. If this is not the case, then the semantics
   *       in formulas that use witness terms may be unintuitive. For example,
   *       the following formula is unsatisfiable:
   *       `(or (= (witness ((x Int)) false) 0) (not (= (witness ((x Int))
   *       false) 0))`, whereas notice that `(or (= z 0) (not (= z 0)))` is
   *       true for any @f$z@f$.
   *
   * - Arity: `3`
   *   - `1:` Term of kind #VARIABLE_LIST
   *   - `2:` Term of Sort Bool (the body of the witness)
   *   - `3:` (optional) Term of kind #INST_PATTERN_LIST
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  WITNESS,

  /* Boolean --------------------------------------------------------------- */

  /**
   * Boolean constant.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTrue() const
   *   - Solver::mkFalse() const
   *   - Solver::mkBoolean(bool) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  APPLY_UF,
  /**
   * Cardinality constraint on uninterpreted sort.
   *
   * Interpreted as a predicate that is true when the cardinality of
   * uinterpreted Sort @f$S@f$ is less than or equal to an upper bound.
   *
   * - Arity: `0`
   * - Create Term of this Kind with:
   *   - Solver::mkCardinalityConstraint(const Sort&, uint32_t) const
   */
  CARDINALITY_CONSTRAINT,
  /**
   * Higher-order applicative encoding of function application, left
   * associative.
   *
   * - Arity: `n = 2`
   *   - `1:` Function Term
   *   - `2:` Argument Term of the domain Sort of the function
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  MULT,
  /**
   * Integer and.
   *
   * Operator for bit-wise `AND` over integers, parameterized by a (positive)
   * bit-width @f$k@f$.
   *
   * \rst
   * .. code:: smtlib
   *
   *     ((_ iand k) i_1 i_2)
   * \endrst
   * is equivalent to
   * \rst
   * .. code:: smtlib
   *
   *     ((_ iand k) i_1 i_2)
   *     (bv2int (bvand ((_ int2bv k) i_1) ((_ int2bv k) i_2)))
   * \endrst
   * for all integers `i_1`, `i_2`.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of Sort Int
   *
   * - Indices: `1`
   *   - `1:` Bit-width @f$k@f$
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  IAND,
  /**
   * Power of two.
   *
   * Operator for raising `2` to a non-negative integer power.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  POW2,
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INTS_DIVISION,
  /**
   * Integer modulus, modulus by 0 undefined.
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SQRT,
  /**
   * Operator for the divisibility-by-@f$k@f$ predicate.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Indices: `1`
   *   - `1:` The integer @f$k@f$ to divide by.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  GEQ,
  /**
   * Is-integer predicate.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  TO_REAL,
  /**
   * Pi constant.
   *
   * @note #PI is considered a special symbol of Sort Real, but is not
   * a Real value, i.e., Term::isRealValue() will return `false`.
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
   *   - Solver::mkBitVector(uint32_t, uint64_t) const
   *   - Solver::mkBitVector(uint32_t, const std::string&, uint32_t) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BITVECTOR_XNOR,
  /**
   * Equality comparison (returns bit-vector of size `1`).
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BITVECTOR_NEG,
  /**
   * Unsigned bit-vector division.
   *
   * Truncates towards `0`. If the divisor is zero, the result is all ones.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BITVECTOR_ULTBV,
  /**
   * Bit-vector signed less than returning a bit-vector of size `1`.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BITVECTOR_SLTBV,
  /**
   * Bit-vector if-then-else.
   *
   * Same semantics as regular ITE, but condition is bit-vector of size `1`.
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BITVECTOR_REDAND,
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BITVECTOR_ROTATE_RIGHT,
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkRoundingMode(RoundingMode rm) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  CONST_ARRAY,
  /**
   * Equality over arrays @f$a@f$ and @f$b@f$ over a given range @f$[i,j]@f$,
   * i.e.,
   * @f[
   *   \forall k . i \leq k \leq j \Rightarrow a[k] = b[k]
   * @f]
   *
   * @note We currently support the creation of array equalities over index
   *       Sorts bit-vector, floating-point, Int and Real.
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   */
  EQ_RANGE,

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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - `2:` Term of Datatype Sort (DatatypeSelector of the updater must
   *          belong to a constructor of this Datatype Sort)
   *   - `3:` Term of the codomain Sort of the selector (the Term to update
   *          the field of the datatype term with)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  APPLY_UPDATER,
  /**
   * Match expression.
   
   * This kind is primarily used in the parser to support the
   * SMT-LIBv2 `match` expression.
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  MATCH,
  /**
   * Match case for nullary constructors.
   *
   * A (constant) case expression to be used within a match expression.
   *
   * - Arity: `2`
   *   - `1:` Term of kind #APPLY_CONSTRUCTOR (the pattern to match against)
   *   - `2:` Term of any Sort (the term the match term evaluates to)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *     - `3:` Term of any Sort (the term the pattern evaluates to)
   *   - For constructors with selectors:
   *     - `1:` Term of kind #VARIABLE_LIST (containing the free variable of
   *            the case)
   *     - `2:` Term of kind #APPLY_CONSTRUCTOR (the pattern expression,
   *            applying the set of variables to the constructor)
   *     - `3:` Term of any Sort (the term the match term evaluates to)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  TUPLE_PROJECT,

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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEP_WAND,

  /* Sets ------------------------------------------------------------------ */

  /**
   * Empty set.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkEmptySet(const Sort&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SET_SUBSET,
  /**
   * Set membership predicate.
   *
   * Determines if the given set element is a member of the second set.
   *
   * - Arity: `2`
   *   - `1:` Term of any Sort (must match the element Sort of the
   *          given set Term)
   *   - `2:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SET_MEMBER,
  /**
   * Singleton set.
   *
   * Construct a singleton set from an element given as a parameter.
   * The returned set has the same Sort as the element.
   *
   * - Arity: `1`
   *   - `1:` Term of any Sort (the set element)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SET_COMPLEMENT,
  /**
   * Finite universe set.
   *
   * All set variables must be interpreted as subsets of it.
   *
   * @note #SET_UNIVERSE is considered a special symbol of the theory of
   *       sets and is not considered as a set value, i.e.,
   *       Term::isSetValue() will return `false`.
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
   *  \forall y. ( \exists x_1...x_n. P[x_1...x_n] \wedge t[x_1...x_n] = y )
   * \Leftrightarrow (set.member \; y \; C)
   * @f]
   * where @f$y@f$ ranges over the element Sort of the (set) Sort of the
   * comprehension. If @f$t[x_1..x_n]@f$ is not provided, it is equivalent
   * to @f$y@f$ in the above formula.
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SET_COMPREHENSION,
  /**
   * Set choose.
   *
   * Select an element from a given set. For a set @f$A = \{x\}@f$, the term
   * `(set.choose A)` is equivalent to the term @f$x@f$. For an empty set,
   * it is an arbitrary value. For a set with cardinality > 1, it will
   * deterministically return an element in @f$A@f$.
   *
   * - Arity: `1`
   *   - `1:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
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
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SET_IS_SINGLETON,
  /**
   * Set map.
   *
   * This operator applies the first argument, a function of
   * Sort @f$(\rightarrow S_1 \; S_2)@f$, to every element of the second
   * argument, a set of Sort (Set @f$S_1@f$), and returns a set of Sort
   * (Set @f$S_2@f$).
   *
   * - Arity: `2`
   *   - `1:` Term of function Sort @f$(\rightarrow S_1 \; S_2)@f$
   *   - `2:` Term of set Sort (Set @f$S_1@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
   SET_MAP,

  /* Relations ------------------------------------------------------------- */

  /**
   * Relation join.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of relation Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  RELATION_JOIN,
  /**
   * Relation cartesian product.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of relation Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  RELATION_PRODUCT,
  /**
   * Relation transpose.
   *
   * - Arity: `1`
   *   - `1:` Term of relation Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  RELATION_TRANSPOSE,
  /**
   * Relation transitive closure.
   *
   * - Arity: `1`
   *   - `1:` Term of relation Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  RELATION_TCLOSURE,
  /**
   * Relation join image.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of relation Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  RELATION_JOIN_IMAGE,
  /**
   * Relation identity.
   *
   * - Arity: `1`
   *   - `1:` Term of relation Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  RELATION_IDEN,

  /* Bags ------------------------------------------------------------------ */

  /**
   * Empty bag.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkEmptyBag(const Sort&) const
   */
  BAG_EMPTY,
  /**
   * Bag max union.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_UNION_MAX,
  /**
   * Bag disjoint union (sum).
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_UNION_DISJOINT,
  /**
   * Bag intersection (min).
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_INTER_MIN,
  /**
   * Bag difference subtract.
   *
   * Subtracts multiplicities of the second from the first.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_DIFFERENCE_SUBTRACT,
  /**
   * Bag difference remove.
   *
   * Removes shared elements in the two bags.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_DIFFERENCE_REMOVE,
  /**
   * Bag inclusion predicate.
   *
   * Determine if multiplicities of the first bag are less than or equal to
   * multiplicities of the second bag.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_SUBBAG,
  /**
   * Bag element multiplicity.
   *
   * Parameters:
   *   - 1..2: Terms of bag sort (Bag E), [1] an element of sort E
   *
   * Create with:
   *   - Solver::mkTerm(Kind kind, const Term& child1, const Term& child2) const
   *   - Solver::mkTerm(Kind kind, const std::vector<Term>& children) const
   */
  BAG_COUNT,
  /**
   * Bag membership predicate.
   *
   * - Arity: `2`
   *   - `1:` Term of any Sort (must match the element Sort of the
   *          given bag Term)
   *   - `2:` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_MEMBER,
  /**
   * Bag duplicate removal.
   *
   * Eliminate duplicates in a given bag. The returned bag contains exactly the
   * same elements in the given bag, but with multiplicity one.
   *
   * - Arity: `1`
   *   - `1:` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_DUPLICATE_REMOVAL,
  /**
   * Bag make.
   *
   * Construct a bag with the given element and given multiplicity.
   *
   * - Arity: `2`
   *   - `1:` Term of any Sort (the bag element)
   *   - `2:` Term of Sort Int (the multiplicity of the element)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_MAKE,
  /**
   * Bag cardinality.
   *
   * - Arity: `1`
   *   - `1:` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_CARD,
  /**
   * Bag choose.
   *
   * Select an element from a given bag.
   *
   * For a bag @f$A = \{(x,n)\}@f$ where @f$n@f$ is the multiplicity, then the
   * term `(choose A)` is equivalent to the term @f$x@f$. For an empty bag,
   * then it is an arbitrary value. For a bag that contains distinct elements,
   * it will deterministically return an element in @f$A@f$.
   *
   * - Arity: `1`
   *   - `1:` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_CHOOSE,
  /**
   * Bag is singleton tester.
   *
   * - Arity: `1`
   *   - `1:` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_IS_SINGLETON,
  /**
   * Conversion from set to bag.
   *
   * - Arity: `1`
   *   - `1:` Term of set Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_FROM_SET,
  /**
   * Conversion from bag to set.
   *
   * - Arity: `1`
   *   - `1:` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_TO_SET,
  /**
   * Bag map.
   *
   * This operator applies the first argument, a function of
   * Sort @f$(\rightarrow S_1 \; S_2)@f$, to every element of the second
   * argument, a set of Sort (Bag @f$S_1@f$), and returns a set of Sort
   * (Bag @f$S_2@f$).
   *
   * - Arity: `2`
   *   - `1:` Term of function Sort @f$(\rightarrow S_1 \; S_2)@f$
   *   - `2:` Term of bag Sort (Bag @f$S_1@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_MAP,
  /**
   * Bag filter.
   *
   * This operator filters the elements of a bag.
   * `(bag.filter p B)` takes a predicate @f$p@f$ of
   * Sort @f$(\rightarrow S_1 \; S_2)@f$ as a first argument, and a bag @f$@f$
   * of Sort (Bag @f$S@f$) as a second argument, and returns a subbag of Sort
   * (Bag @f$T@f$) that includes all elements of @f$B@f$ that satisfy @f$p@f$
   * with the same multiplicity.
   *
   * - Arity: `2`
   *   - `1:` Term of function Sort @f$(\rightarrow S_1 \; S_2)@f$
   *   - `2:` Term of bag Sort (Bag @f$S_1@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
   BAG_FILTER,
  /**
   * Bag fold.
   *
   * This operator combines elements of a bag into a single value.
   * `(bag.fold f t B)` folds the elements of bag @f$B@f$ starting with
   * Term @f$t@f$ and using the combining function @f$f@f$.
   *
   * - Arity: `2`
   *   - `1:` Term of function Sort @f$(\rightarrow S_1 \; S_2 \; S_2)@f$
   *   - `2:` Term of Sort `S_2)` (the initial value)
   *   - `3:` Term of bag Sort (Bag @f$S_1@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  BAG_FOLD,
  /**
   * Table cross product.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of table Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  TABLE_PRODUCT,

  /* Strings --------------------------------------------------------------- */

  /**
   * String concat.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_CONCAT,
  /**
   * String membership.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String
   *   - `2:` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_IN_REGEXP,
  /**
   * String length.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_LENGTH,
  /**
   * String substring.
   *
   * Extracts a substring, starting at index @f$i@f$ and of length @f$l@f$,
   * from a string @f$s@f$.  If the start index is negative, the start index is
   * greater than the length of the string, or the length is negative, the
   * result is the empty string.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String
   *   - `2:` Term of Sort Int (index @f$i@f$)
   *   - `3:` Term of Sort Int (length @f$l@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_SUBSTR,
  /**
   * String update.
   *
   * Updates a string @f$s@f$ by replacing its context starting at an index
   * with string @f$t@f$. If the start index is negative, the start index is
   * greater than the length of the string, the result is @f$s@f$. Otherwise,
   * the length of the original string is preserved.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String
   *   - `2:` Term of Sort Int (index @f$i@f$)
   *   - `3:` Term of Sort Strong (replacement string @f$t@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_UPDATE,
  /**
   * String character at.
   *
   * Returns the character at index @f$i@f$ from a string @f$s@f$. If the index is
   * negative or the index is greater than the length of the string, the result
   * is the empty string. Otherwise the result is a string of length @f$1@f$.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (string @f$s@f$)
   *   - `2:` Term of Sort Int (index @f$i@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_CHARAT,
  /**
   * String contains.
   *
   * Determines whether a string @f$s_1@f$ contains another string @f$s_2@f$.
   * If @f$s_2@f$ is empty, the result is always `true`.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (the string @f$s_1@f$)
   *   - `2:` Term of Sort String (the string @f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_CONTAINS,
  /**
   * String index-of.
   *
   * Returns the index of a substring @f$s_2@f$ in a string @f$s_1@f$ starting
   * at index @f$i@f$. If the index is negative or greater than the length of
   * string @f$s_1@f$ or the substring @f$s_2@f$ does not appear in
   * string @f$s_1@f$ after index @f$i@f$, the result is `-1`.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (substring @f$s_1@f$)
   *   - `2:` Term of Sort String (substring @f$s_2@f$)
   *   - `3:` Term of Sort Int (index @f$i@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_INDEXOF,
  /**
   * String index-of regular expression match.
   *
   * Returns the first match of a regular expression @f$r@f$ in a
   * string @f$s@f$. If the index is negative or greater than the length of
   * string @f$s_1@f$, or @f$r@f$ does not match a substring in @f$s@f$ after
   * index @f$i@f$, the result is `-1`.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String (string @f$s@f$)
   *   - `2:` Term of Sort RegLan (regular expression @f$r@f$)
   *   - `3:` Term of Sort Int (index @f$i@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_INDEXOF_RE,
  /**
   * String replace.
   *
   * Replaces a string @f$s_2@f$ in a string @f$s_1@f$ with string @f$s_3@f$.
   * If @f$s_2@f$ does not appear in @f$s_1@f$, @f$s_1@f$ is returned
   * unmodified.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String (string @f$s_1@f$)
   *   - `2:` Term of Sort String (string @f$s_2@f$)
   *   - `3:` Term of Sort String (string @f$s_3@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_REPLACE,
  /**
   * String replace all.
   *
   * Replaces all occurrences of a string @f$s_2@f$ in a string @f$s_1@f$ with
   * string @f$s_3@f$. If @f$s_2@f$ does not appear in @f$s_1@f$, @f$s_1@f$ is
   * returned unmodified.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort String (@f$s_2@f$)
   *   - `3:` Term of Sort String (@f$s_3@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_REPLACE_ALL,
  /**
   * String replace regular expression match.
   *
   * Replaces the first match of a regular expression @f$r@f$ in
   * string @f$s_1@f$ with string @f$s_2@f$. If @f$r@f$ does not match a
   * substring of @f$s_1@f$, @f$s_1@f$ is returned unmodified.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort RegLan
   *   - `3:` Term of Sort String (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_REPLACE_RE,
  /**
   * String replace all regular expression matches.
   *
   * Replaces all matches of a regular expression @f$r@f$ in string @f$s_1@f$
   * with string @f$s_2@f$. If @f$r@f$ does not match a substring of @f$s_1@f$,
   * string @f$s_1@f$ is returned unmodified.
   *
   * - Arity: `3`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort RegLan
   *   - `3:` Term of Sort String (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_REPLACE_RE_ALL,
  /**
   * String to lower case.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_TO_LOWER,
  /**
   * String to upper case.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_TO_UPPER,
  /**
   * String reverse.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_REV,
  /**
   * String to code.
   *
   * Returns the code point of a string if it has length one, or returns `-1`
   * otherwise.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_TO_CODE,
  /**
   * String from code.
   *
   * Returns a string containing a single character whose code point matches
   * the argument to this function, or the empty string if the argument is
   * out-of-bounds.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_FROM_CODE,
  /**
   * String less than.
   *
   * Returns true if string @f$s_1@f$ is (strictly) less than @f$s_2@f$ based
   * on a lexiographic ordering over code points.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort String (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_LT,
  /**
   * String less than or equal.
   *
   * Returns true if string @f$s_1@f$ is less than or equal to @f$s_2@f$ based
   * on a lexiographic ordering over code points.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort String (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_LEQ,
  /**
   * String prefix-of.
   *
   * Determines whether a string @f$s_1@f$ is a prefix of string @f$s_2@f$.
   * If string s1 is empty, this operator returns `true`.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort String (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_PREFIX,
  /**
   * String suffix-of.
   *
   * Determines whether a string @f$s_1@f$ is a suffix of the second string.
   * If string @f$s_1@f$ is empty, this operator returns `true`.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (@f$s_1@f$)
   *   - `2:` Term of Sort String (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_SUFFIX,
  /**
   * String is-digit.
   *
   * Returns true if given string is a digit (it is one of `"0"`, ..., `"9"`).
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_IS_DIGIT,
  /**
   * Conversion from Int to String.
   *
   * If the integer is negative this operator returns the empty string.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_FROM_INT,
  /**
   * String to integer (total function).
   *
   * If the string does not contain an integer or the integer is negative, the
   * operator returns `-1`.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_TO_INT,
  /**
   * Constant string.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkString(const std::string&, bool) const
   *   - Solver::mkString(const std::wstring&) const
   */
  CONST_STRING,
  /**
   * Conversion from string to regexp.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort String
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  STRING_TO_REGEXP,
  /**
   * Regular expression concatenation.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_CONCAT,
  /**
   * Regular expression union.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_UNION,
  /**
   * Regular expression intersection.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_INTER,
  /**
   * Regular expression difference.
   *
   * - Arity: `2`
   *   - `1..2:` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_DIFF,
  /**
   * Regular expression \*.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_STAR,
  /**
   * Regular expression +.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_PLUS,
  /**
   * Regular expression ?.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_OPT,
  /**
   * Regular expression range.
   *
   * - Arity: `2`
   *   - `1:` Term of Sort String (lower bound character for the range)
   *   - `2:` Term of Sort String (upper bound character for the range)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_RANGE,
  /**
   * Operator for regular expression repeat.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort RegLan
   *
   * - Indices: `1`
   *   - `1:` The number of repetitions
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_REPEAT,
  /**
   * Regular expression loop.
   *
   * Regular expression loop from lower bound to upper bound number of
   * repetitions.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort RegLan
   *
   * - Indices: `1`
   *   - `1:` The lower bound
   *   - `2:` The upper bound
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_LOOP,
  /**
   * Regular expression none.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkRegexpNone() const
   */
  REGEXP_NONE,
  /**
   * Regular expression all.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkRegexpAll() const
   */
  REGEXP_ALL,
  /**
   * Regular expression all characters.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkRegexpAllchar() const
   */
  REGEXP_ALLCHAR,
  /**
   * Regular expression complement.
   *
   * - Arity: `1`
   *   - `1:` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  REGEXP_COMPLEMENT,

  /**
   * Sequence concat.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of sequence Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_CONCAT,
  /**
   * Sequence length.
   *
   * - Arity: `1`
   *   - `1:` Term of sequence Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_LENGTH,
  /**
   * Sequence extract.
   *
   * Extracts a subsequence, starting at index @f$i@f$ and of length @f$l@f$,
   * from a sequence @f$s@f$.  If the start index is negative, the start index
   * is greater than the length of the sequence, or the length is negative, the
   * result is the empty sequence.
   *
   * - Arity: `3`
   *   - `1:` Term of sequence Sort
   *   - `2:` Term of Sort Int (index @f$i@f$)
   *   - `3:` Term of Sort Int (length @f$l@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_EXTRACT,
  /**
   * Sequence update.
   *
   * Updates a sequence @f$s@f$ by replacing its context starting at an index
   * with string @f$t@f$. If the start index is negative, the start index is
   * greater than the length of the sequence, the result is @f$s@f$. Otherwise,
   * the length of the original sequence is preserved.
   *
   * - Arity: `3`
   *   - `1:` Term of sequence Sort
   *   - `2:` Term of Sort Int (index @f$i@f$)
   *   - `3:` Term of sequence Sort (replacement sequence @f$t@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_UPDATE,
  /**
   * Sequence element at.
   *
   * Returns the element at index @f$i@f$ from a sequence @f$s@f$. If the index
   * is negative or the index is greater or equal to the length of the
   * sequence, the result is the empty sequence. Otherwise the result is a
   * sequence of length `1`.
   *
   * - Arity: `2`
   *   - `1:` Term of sequence Sort
   *   - `2:` Term of Sort Int (index @f$i@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_AT,
  /**
   * Sequence contains.
   *
   * Checks whether a sequence @f$s_1@f$ contains another sequence @f$s_2@f$.
   * If @f$s_2@f$ is empty, the result is always `true`.
   *
   * - Arity: `2`
   *   - `1:` Term of sequence Sort (@f$s_1@f$)
   *   - `2:` Term of sequence Sort (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_CONTAINS,
  /**
   * Sequence index-of.
   *
   * Returns the index of a subsequence @f$s_2@f$ in a sequence @f$s_1@f$
   * starting at index @f$i@f$. If the index is negative or greater than the
   * length of sequence @f$s_1@f$ or the subsequence @f$s_2@f$ does not appear
   * in sequence @f$s_1@f$ after index @f$i@f$, the result is `-1`.
   *
   * - Arity: `3`
   *   - `1:` Term of sequence Sort (@f$s_1@f$)
   *   - `2:` Term of sequence Sort (@f$s_2@f$)
   *   - `3:` Term of Sort Int (@f$i@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_INDEXOF,
  /**
   * Sequence replace.
   *
   * Replaces the first occurrence of a sequence @f$s_2@f$ in a
   * sequence @f$s_1@f$ with sequence @f$s_3@f$. If @f$s_2@f$ does not
   * appear in @f$s_1@f$, @f$s_1@f$ is returned unmodified.
   *
   * - Arity: `3`
   *   - `1:` Term of sequence Sort (@f$s_1@f$)
   *   - `2:` Term of sequence Sort (@f$s_2@f$)
   *   - `3:` Term of sequence Sort (@f$s_3@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_REPLACE,
  /**
   * Sequence replace all.
   *
   * Replaces all occurrences of a sequence @f$s_2@f$ in a sequence @f$s_1@f$
   * with sequence @f$s_3@f$. If @f$s_2@f$ does not appear in @f$s_1@f$,
   * sequence @f$s_1@f$ is returned unmodified.
   *
   * - Arity: `3`
   *   - `1:` Term of sequence Sort (@f$s_1@f$)
   *   - `2:` Term of sequence Sort (@f$s_2@f$)
   *   - `3:` Term of sequence Sort (@f$s_3@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_REPLACE_ALL,
  /**
   * Sequence reverse.
   *
   * - Arity: `1`
   *   - `1:` Term of sequence Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_REV,
  /**
   * Sequence prefix-of.
   *
   * Checks whether a sequence @f$s_1@f$ is a prefix of sequence @f$s_2@f$. If
   * sequence @f$s_1@f$ is empty, this operator returns `true`.
   *
   * - Arity: `1`
   *   - `1:` Term of sequence Sort (@f$s_1@f$)
   *   - `2:` Term of sequence Sort (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_PREFIX,
  /**
   * Sequence suffix-of.
   *
   * Checks whether a sequence @f$s_1@f$ is a suffix of sequence @f$s_2@f$. If
   * sequence @f$s_1@f$ is empty, this operator returns `true`.
   *
   * - Arity: `1`
   *   - `1:` Term of sequence Sort (@f$s_1@f$)
   *   - `2:` Term of sequence Sort (@f$s_2@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_SUFFIX,
  /**
   * Constant sequence.
   *
   * A constant sequence is a term that is equivalent to:
   * \rst
   * .. code:: smtlib
   *
   *     (seq.++ (seq.unit c1) ... (seq.unit cn))
   * \endrst
   * where @f$n \leq 0@f$ and @f$c_1, ..., c_n@f$ are constants of some sort.
   * The elements can be extracted with Term::getSequenceValue().
   *
   * - Create Term of this Kind with:
   *   - Solver::mkEmptySequence(const Sort&) const
   */
  CONST_SEQUENCE,
  /**
   * Sequence unit.
   *
   * Corresponds to a sequence of length one with the given term.
   *
   * - Arity: `1`
   *   - `1:` Term of any Sort (the element term)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_UNIT,
  /**
   * Sequence nth.
   *
   * Corresponds to the nth element of a sequence.
   *
   * - Arity: `2`
   *   - `1:` Term of sequence Sort
   *   - `2:` Term of Sort Int (@f$n@f$)
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SEQ_NTH,

  /* Quantifiers ----------------------------------------------------------- */

  /**
   * Universally quantified formula.
   *
   * - Arity: `3`
   *   - `1:` Term of Kind #VARIABLE_LIST
   *   - `2:` Term of Sort Bool (the quantifier body)
   *   - `3:` (optional) Term of Kind #INST_PATTERN
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  FORALL,
  /**
   * Existentially quantified formula.
   *
   * - Arity: `3`
   *   - `1:` Term of Kind #VARIABLE_LIST
   *   - `2:` Term of Sort Bool (the quantifier body)
   *   - `3:` (optional) Term of Kind #INST_PATTERN
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EXISTS,
  /**
   * Variable list.
   *
   * A list of variables (used to bind variables under a quantifier)
   *
   * - Arity: `n > 0`
   *   - `1..n:` Terms of Kind #VARIABLE
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  VARIABLE_LIST,
  /**
   * Instantiation pattern.
   *
   * Specifies a (list of) terms to be used as a pattern for quantifier
   * instantiation.
   *
   * @note Should only be used as a child of #INST_PATTERN_LIST.
   *
   * - Arity: `n > 0`
   *   - `1..n:` Terms of any Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INST_PATTERN,
  /**
   * Instantiation no-pattern.
   *
   * Specifies a (list of) terms that should not be used as a pattern for
   * quantifier instantiation.
   *
   * @note Should only be used as a child of #INST_PATTERN_LIST.
   *
   * - Arity: `n > 0`
   *   - `1..n:` Terms of any Sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INST_NO_PATTERN,
  /**
   * Instantiation pool annotation.
   *
   * Specifies an annotation for pool based instantiation.
   *
   * @note Should only be used as a child of #INST_PATTERN_LIST.
   *
   * In detail, pool symbols can be declared via the method
   *  - Solver::declarePool(const std::string&, const Sort&, const std::vector<Term>&) const
   *
   * A pool symbol represents a set of terms of a given sort. An instantiation
   * pool annotation should match the types of the quantified formula.
   *
   * For example, for a quantified formula:
   *
   * \rst
   * .. code:: lisp
   *
   *     (FORALL (VARIABLE_LIST x y) F (INST_PATTERN_LIST (INST_POOL p q)))
   * \endrst
   *
   * if @f$x@f$ and @f$y@f$ have Sorts @f$S_1@f$ and @f$S_2@f$,
   * then pool symbols @f$p@f$ and @f$q@f$ should have Sorts
   * (Set @f$S_1@f$) and (Set @f$S_2@f$), respectively.
   * This annotation specifies that the quantified formula above should be
   * instantiated with the product of all terms that occur in the sets @f$p@f$
   * and @f$q@f$.
   * 
   * - Arity: `n > 0`
   *   - `1..n:` Terms that comprise the pools, which are one-to-one with the
   *             variables of the quantified formula to be instantiated
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INST_POOL,
  /**
   * A instantantiation-add-to-pool annotation.
   *
   * @note Should only be used as a child of #INST_PATTERN_LIST.
   * 
   * An instantantiation-add-to-pool annotation indicates that when a quantified
   * formula is instantiated, the instantiated version of a term should be
   * added to the given pool.
   * 
   * For example, consider a quantified formula:
   * 
   * \rst
   * .. code:: lisp
   *
   *     (FORALL (VARIABLE_LIST x) F 
   *             (INST_PATTERN_LIST (INST_ADD_TO_POOL (ADD x 1) p)))
   * \endrst
   * 
   * where assume that @f$x@f$ has type Int. When this quantified formula is
   * instantiated with, e.g., the term @f$t@f$, the term `(ADD t 1)` is added to pool @f$p@f$.
   *
   * - Arity: `2`
   *   - `1:` The Term whose free variables are bound by the quantified formula.
   *   - `2:` The pool to add to, whose Sort should be a set of elements that
   *          match the Sort of the first argument.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INST_ADD_TO_POOL,
  /**
   * A skolemization-add-to-pool annotation.
   *
   * @note Should only be used as a child of #INST_PATTERN_LIST.
   *
   * An skolemization-add-to-pool annotation indicates that when a quantified
   * formula is skolemized, the skolemized version of a term should be added to
   * the given pool.
   *
   * For example, consider a quantified formula:
   *
   * \rst
   * .. code:: lisp
   *
   *     (FORALL (VARIABLE_LIST x) F
   *             (INST_PATTERN_LIST (SKOLEM_ADD_TO_POOL (ADD x 1) p)))
   * \endrst
   *
   * where assume that @f$x@f$ has type Int. When this quantified formula is
   * skolemized, e.g., with @f$k@f$ of type Int, then the term `(ADD k 1)` is
   * added to the pool @f$p@f$.
   *
   * - Arity: `2`
   *   - `1:` The Term whose free variables are bound by the quantified formula.
   *   - `2:` The pool to add to, whose Sort should be a set of elements that
   *          match the Sort of the first argument.
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  SKOLEM_ADD_TO_POOL,
  /**
   * Instantiation attribute.
   *
   * Specifies a custom property for a quantified formula given by a
   * term that is ascribed a user attribute.
   *
   * @note Should only be used as a child of #INST_PATTERN_LIST.
   *
   * - Arity: `n > 0`
   *   - `1:` Term of Kind #CONST_STRING (the keyword of the attribute)
   *   - `2...n:` Terms representing the values of the attribute
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INST_ATTRIBUTE,
  /**
   * A list of instantiation patterns, attributes or annotations.
   *
   * - Arity: `n > 1`
   *   - `1..n:` Terms of Kind #INST_PATTERN, #INST_NO_PATTERN, #INST_POOL,
   *             #INST_ADD_TO_POOL, #SKOLEM_ADD_TO_POOL, #INST_ATTRIBUTE
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  INST_PATTERN_LIST,

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

}  // namespace cvc5::api

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
