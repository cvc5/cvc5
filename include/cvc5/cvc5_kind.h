/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The term kinds of the cvc5 C++ and C APIs.
 */

#if (!defined(CVC5_API_USE_C_ENUMS) && !defined(CVC5__API__CVC5_CPP_KIND_H)) \
    || (defined(CVC5_API_USE_C_ENUMS) && !defined(CVC5__API__CVC5_C_KIND_H))

#ifdef CVC5_API_USE_C_ENUMS
#include <stddef.h>
#include <stdint.h>
#undef ENUM
#define ENUM(name) Cvc5##name
#else
#include <cvc5/cvc5_export.h>

#include <cstdint>
#include <ostream>
namespace cvc5 {
#undef ENUM
#define ENUM(name) class name
#undef EVALUE
#define EVALUE(name) name
#endif

/* -------------------------------------------------------------------------- */
/* Kind                                                                       */
/* -------------------------------------------------------------------------- */

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_KIND_##name
#endif

// clang-format off
/**
 * The kind of a cvc5 Term.
 *
 * \internal
 *
 * Note that the API type `cvc5::Kind` roughly corresponds to
 * `cvc5::internal::Kind`, but is a different type. It hides internal kinds
 * that should not be exported to the API, and maps all kinds that we want to
 * export to its corresponding internal kinds. The underlying type of
 * `cvc5::Kind` must be signed (to enable range checks for validity). The size
 * of this type depends on the size of `cvc5::internal::Kind`
 * (`NodeValue::NBITS_KIND`, currently 10 bits, see expr/node_value.h).
 */
enum ENUM(Kind) : int32_t
{
  /**
   * Internal kind.
   *
   * This kind serves as an abstraction for internal kinds that are not exposed
   * via the API but may appear in terms returned by API functions, e.g.,
   * when querying the simplified form of a term.
   *
   * \rst
   * .. note:: Should never be created via the API.
   * \endrst
   */
  EVALUE(INTERNAL_KIND = -2),
  /**
   * Undefined kind.
   *
   * \rst
   * .. note:: Should never be exposed or created via the API.
   * \endrst
   */
  EVALUE(UNDEFINED_KIND = -1),
  /**
   * Null kind.
   *
   * The kind of a null term (Term::Term()).
   *
   * \rst
   * .. note:: May not be explicitly created via API functions other than
   *           :cpp:func:`Term::Term()`.
   * \endrst
   */
  EVALUE(NULL_TERM),

  /* Builtin --------------------------------------------------------------- */

  /**
   * The value of an uninterpreted constant.
   *
   * \rst
   * .. note:: May be returned as the result of an API call, but terms of this
   *           kind may not be created explicitly via the API and may not
   *           appear in assertions.
   * \endrst
   */
  EVALUE(UNINTERPRETED_SORT_VALUE),
  /**
   * Equality, chainable.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of the same Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(EQUAL),
  /**
   * Disequality.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of the same Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(DISTINCT),
  /**
   * Free constant symbol.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkConst(const Sort&, const std::string&) const
   *   - Solver::mkConst(const Sort&) const
   *
   * \rst
   * .. note:: Not permitted in bindings (e.g., :cpp:enumerator:`FORALL`,
   *           :cpp:enumerator:`EXISTS`).
   * \endrst
   */
  EVALUE(CONSTANT),
  /**
   * (Bound) variable.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkVar(const Sort&, const std::string&) const
   *
   * \rst
   * .. note:: Only permitted in bindings and in lambda and quantifier bodies.
   * \endrst
   */
  EVALUE(VARIABLE),
  /**
   * A Skolem.
   *
   * \rst
   * .. note:: Represents an internally generated term. Information on the
   * skolem is available via the calls `Solver::getSkolemId` and
   * `Solver::getSkolemIndices`.
   * \endrst
   */
  EVALUE(SKOLEM),
  /**
   * Symbolic expression.
   *
   * - Arity: ``n > 0``
   *
   *   - ``1..n:`` Terms with same sorts
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SEXPR),
  /**
   * Lambda expression.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of kind :cpp:enumerator:`VARIABLE_LIST`
   *   - ``2:`` Term of any Sort (the body of the lambda)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(LAMBDA),
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
   *
   * returns an element :math:`x` of Sort :math:`S` and asserts formula
   * :math:`F`.
   *
   * The witness operator behaves like the description operator
   * (see https://planetmath.org/hilbertsvarepsilonoperator) if there is
   * no :math:`x` that satisfies :math:`F`. But if such :math:`x` exists, the
   * witness operator does not enforce the following axiom which ensures
   * uniqueness up to logical equivalence:
   *
   * .. math::
   *
   *     \forall x. F \equiv G \Rightarrow witness~x. F =  witness~x. G
   *
   * For example, if there are two elements of Sort :math:`S` that satisfy
   * formula :math:`F`, then the following formula is satisfiable:
   *
   * .. code:: smtlib
   *
   *     (distinct
   *        (witness ((x Int)) F)
   *        (witness ((x Int)) F))
   *
   * \endrst
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of kind :cpp:enumerator:`VARIABLE_LIST`
   *   - ``2:`` Term of Sort Bool (the body of the witness)
   *   - ``3:`` (optional) Term of kind :cpp:enumerator:`INST_PATTERN_LIST`
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. note::
   *
   *     This kind is primarily used internally, but may be returned in
   *     models (e.g., for arithmetic terms in non-linear queries). However,
   *     it is not supported by the parser. Moreover, the user of the API
   *     should be cautious when using this operator. In general, all witness
   *     terms ``(witness ((x Int)) F)`` should be such that ``(exists ((x Int))
   *     F)`` is a valid formula. If this is not the case, then the semantics
   *     in formulas that use witness terms may be unintuitive. For example,
   *     the following formula is unsatisfiable:
   *     ``(or (= (witness ((x Int)) false) 0) (not (= (witness ((x Int))
   *     false) 0))``, whereas notice that ``(or (= z 0) (not (= z 0)))`` is
   *     true for any :math:`z`.
   * \endrst
   */
  EVALUE(WITNESS),

  /* Boolean --------------------------------------------------------------- */

  /**
   * Boolean constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTrue() const
   *   - Solver::mkFalse() const
   *   - Solver::mkBoolean(bool) const
   */
  EVALUE(CONST_BOOLEAN),
  /**
   * Logical negation.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Bool
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(NOT),
  /**
   * Logical conjunction.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(AND),
  /**
   * Logical implication.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(IMPLIES),
  /**
   * Logical disjunction.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(OR),
  /**
   * Logical exclusive disjunction, left associative.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Bool
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(XOR),
  /**
   * If-then-else.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort Bool
   *   - ``2:`` The 'then' term, Term of any Sort
   *   - ``3:`` The 'else' term, Term of the same sort as second argument
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ITE),

  /* UF -------------------------------------------------------------------- */

  /**
   * Application of an uninterpreted function.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1:`` Function Term
   *   - ``2..n:`` Function argument instantiation Terms of any first-class Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(APPLY_UF),
  /**
   * Cardinality constraint on uninterpreted sort.
   *
   * \rst
   * Interpreted as a predicate that is true when the cardinality of
   * uinterpreted Sort :math:`S` is less than or equal to an upper bound.
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkCardinalityConstraint(const Sort&, uint32_t) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(CARDINALITY_CONSTRAINT),
  /**
   * Higher-order applicative encoding of function application, left
   * associative.
   *
   * - Arity: ``n = 2``
   *
   *   - ``1:`` Function Term
   *   - ``2:`` Argument Term of the domain Sort of the function
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(HO_APPLY),

  /* Arithmetic ------------------------------------------------------------ */

  /**
   * Arithmetic addition.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ADD),
  /**
   * Arithmetic multiplication.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(MULT),
  /**
   * Integer and.
   *
   * \rst
   * Operator for bit-wise ``AND`` over integers, parameterized by a (positive)
   * bit-width :math:`k`.
   *
   * .. code:: smtlib
   *
   *     ((_ iand k) i_1 i_2)
   *
   * is equivalent to
   *
   * .. code:: smtlib
   *
   *     ((_ iand k) i_1 i_2)
   *     (bv2int (bvand ((_ int2bv k) i_1) ((_ int2bv k) i_2)))
   *
   * for all integers ``i_1``, ``i_2``.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of Sort Int
   *
   * - Indices: ``1``
   *
   *   - ``1:`` Bit-width :math:`k`
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(IAND),
  /**
   * Power of two.
   *
   * Operator for raising ``2`` to a non-negative integer power.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(POW2),
  /**
   * Arithmetic subtraction, left associative.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SUB),
  /**
   * Arithmetic negation.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(NEG),
  /**
   * Real division, division by 0 undefined, left associative.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(DIVISION),
  /**
   * Real division, division by 0 defined to be 0, left associative.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   */
  EVALUE(DIVISION_TOTAL),
  /**
   * Integer division, division by 0 undefined, left associative.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(INTS_DIVISION),
  /**
   * Integer division, division by 0 defined to be 0, left associative.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   */
  EVALUE(INTS_DIVISION_TOTAL),
  /**
   * Integer modulus, modulus by 0 undefined.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort Int
   *   - ``2:`` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(INTS_MODULUS),
  /**
   * Integer modulus, modulus by 0 defined to be 0.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort Int
   *   - ``2:`` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   */
  EVALUE(INTS_MODULUS_TOTAL),
  /**
   * Absolute value.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ABS),
  /**
   * Arithmetic power.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Term of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(POW),
  /**
   * Exponential function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(EXPONENTIAL),
  /**
   * Sine function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SINE),
  /**
   * Cosine function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(COSINE),
  /**
   * Tangent function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(TANGENT),
  /**
   * Cosecant function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(COSECANT),
  /**
   * Secant function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SECANT),
  /**
   * Cotangent function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(COTANGENT),
  /**
   * Arc sine function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ARCSINE),
  /**
   * Arc cosine function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ARCCOSINE),
  /**
   * Arc tangent function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ARCTANGENT),
  /**
   * Arc cosecant function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ARCCOSECANT),
  /**
   * Arc secant function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ARCSECANT),
  /**
   * Arc cotangent function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(ARCCOTANGENT),
  /**
   * Square root.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SQRT),
  /**
   * \rst
   * Operator for the divisibility-by-:math:`k` predicate.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The integer :math:`k` to divide by.
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(DIVISIBLE),
  /**
   * Arbitrary-precision rational constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkReal(const std::string&) const
   *   - Solver::mkReal(int64_t) const
   *   - Solver::mkReal(int64_t, int64_t) const
   */
  EVALUE(CONST_RATIONAL),
  /**
   * Arbitrary-precision integer constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkInteger(const std::string&) const
   *   - Solver::mkInteger(int64_t) const
   */
  EVALUE(CONST_INTEGER),
  /**
   * Less than, chainable.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(LT),
  /**
   * Less than or equal, chainable.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(LEQ),
  /**
   * Greater than, chainable.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(GT),
  /**
   * Greater than or equal, chainable.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort Int or Real (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(GEQ),
  /**
   * Is-integer predicate.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(IS_INTEGER),
  /**
   * Convert Term of sort Int or Real to Int via the floor function.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(TO_INTEGER),
  /**
   * Convert Term of Sort Int or Real to Real.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int or Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(TO_REAL),
  /**
   * Pi constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkPi() const
   *
   * \rst
   * .. note:: :cpp:enumerator:`PI` is considered a special symbol of Sort
   *            Real, but is not a Real value, i.e.,
   *            :cpp:func:`Term::isRealValue()` will return ``false``.
   * \endrst
   */
  EVALUE(PI),

  /* BV -------------------------------------------------------------------- */

  /**
   * Fixed-size bit-vector constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkBitVector(uint32_t, uint64_t) const
   *   - Solver::mkBitVector(uint32_t, const std::string&, uint32_t) const
   */
  EVALUE(CONST_BITVECTOR),
  /**
   * Concatenation of two or more bit-vectors.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_CONCAT),
  /**
   * Bit-wise and.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_AND),
  /**
   * Bit-wise or.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_OR),
  /**
   * Bit-wise xor.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_XOR),
  /**
   * Bit-wise negation.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_NOT),
  /**
   * Bit-wise nand.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_NAND),
  /**
   * Bit-wise nor.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_NOR),
  /**
   * Bit-wise xnor, left associative.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_XNOR),
  /**
   * Equality comparison (returns bit-vector of size ``1``).
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_COMP),
  /**
   * Multiplication of two or more bit-vectors.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_MULT),
  /**
   * Addition of two or more bit-vectors.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ADD),
  /**
   * Subtraction of two bit-vectors.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SUB),
  /**
   * Negation of a bit-vector (two's complement).
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_NEG),
  /**
   * Unsigned bit-vector division.
   *
   * Truncates towards ``0``. If the divisor is zero, the result is all ones.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_UDIV),
  /**
   * Unsigned bit-vector remainder.
   *
   * Remainder from unsigned bit-vector division. If the modulus is zero, the
   * result is the dividend.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_UREM),
  /**
   * Signed bit-vector division.
   *
   * Two's complement signed division of two bit-vectors. If the divisor is
   * zero and the dividend is positive, the result is all ones. If the divisor
   * is zero and the dividend is negative, the result is one.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SDIV),
  /**
   * Signed bit-vector remainder (sign follows dividend).
   *
   * Two's complement signed remainder of two bit-vectors where the sign
   * follows the dividend. If the modulus is zero, the result is the dividend.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SREM),
  /**
   * Signed bit-vector remainder (sign follows divisor).
   *
   * Two's complement signed remainder where the sign follows the divisor. If
   * the modulus is zero, the result is the dividend.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SMOD),
  /**
   * Bit-vector shift left.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SHL),
  /**
   * Bit-vector logical shift right.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_LSHR),
  /**
   * Bit-vector arithmetic shift right.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ASHR),
  /**
   * Bit-vector unsigned less than.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ULT),
  /**
   * Bit-vector unsigned less than or equal.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ULE),
  /**
   * Bit-vector unsigned greater than.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_UGT),
  /**
   * Bit-vector unsigned greater than or equal.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_UGE),
  /**
   * Bit-vector signed less than.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SLT),
  /**
   * Bit-vector signed less than or equal.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SLE),
  /**
   * Bit-vector signed greater than.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SGT),
  /**
   * Bit-vector signed greater than or equal.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SGE),
  /**
   * Bit-vector unsigned less than returning a bit-vector of size 1.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ULTBV),
  /**
   * Bit-vector signed less than returning a bit-vector of size ``1``.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SLTBV),
  /**
   * Bit-vector if-then-else.
   *
   * Same semantics as regular ITE, but condition is bit-vector of size ``1``.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of bit-vector Sort of size `1`
   *   - ``1..3:`` Terms of bit-vector sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ITE),
  /**
   * Bit-vector redor.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_REDOR),
  /**
   * Bit-vector redand.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_REDAND),
  /**
   * Bit-vector negation overflow detection.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_NEGO),
  /**
   * Bit-vector unsigned addition overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_UADDO),
  /**
   * Bit-vector signed addition overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SADDO),
  /**
   * Bit-vector unsigned multiplication overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_UMULO),
  /**
   * Bit-vector signed multiplication overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SMULO),
  /**
   * Bit-vector unsigned subtraction overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_USUBO),
  /**
   * Bit-vector signed subtraction overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SSUBO),
  /**
   * Bit-vector signed division overflow detection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bit-vector Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SDIVO),
  /**
   * Bit-vector extract.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``2``
   *
   *   - ``1:`` The upper bit index.
   *   - ``2:`` The lower bit index.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_EXTRACT),
  /**
   * Bit-vector repeat.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The number of times to repeat the given term.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_REPEAT),
  /**
   * Bit-vector zero extension.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The number of zeroes to extend the given term with.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ZERO_EXTEND),
  /**
   * Bit-vector sign extension.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The number of bits (of the value of the sign bit) to extend the given term with.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_SIGN_EXTEND),
  /**
   * Bit-vector rotate left.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The number of bits to rotate the given term left.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ROTATE_LEFT),
  /**
   * Bit-vector rotate right.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The number of bits to rotate the given term right.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_ROTATE_RIGHT),
  /**
   * Conversion from Int to bit-vector.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The size of the bit-vector to convert to.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(INT_TO_BITVECTOR),
  /**
   * Bit-vector conversion to (non-negative) integer.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BITVECTOR_TO_NAT),

  /* Finite Fields --------------------------------------------------------- */

  /**
   * Finite field constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkFiniteFieldElem(const std::string&, const Sort&, uint32_t base) const
   */
  EVALUE(CONST_FINITE_FIELD),
  /**
   * Negation of a finite field element (additive inverse).
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of finite field Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FINITE_FIELD_NEG),
  /**
   * Addition of two or more finite field elements.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of finite field Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FINITE_FIELD_ADD),
  /**
   * Bitsum of two or more finite field elements: x + 2y + 4z + ...
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of finite field Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   */
  EVALUE(FINITE_FIELD_BITSUM),
  /**
   * Multiplication of two or more finite field elements.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of finite field Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FINITE_FIELD_MULT),

  /* FP -------------------------------------------------------------------- */

  /**
   * Floating-point constant, created from IEEE-754 bit-vector representation
   * of the floating-point value.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkFloatingPoint(uint32_t, uint32_t, Term) const
   */
  EVALUE(CONST_FLOATINGPOINT),
  /**
   * RoundingMode constant.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkRoundingMode(RoundingMode) const
   */
  EVALUE(CONST_ROUNDINGMODE),
  /**
   * Create floating-point literal from bit-vector triple.
   *
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of bit-vector Sort of size `1` (sign bit)
   *   - ``2:`` Term of bit-vector Sort of exponent size (exponent)
   *   - ``3:`` Term of bit-vector Sort of significand size - 1 (significand without hidden bit)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_FP),
  /**
   * Floating-point equality.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_EQ),
  /**
   * Floating-point absolute value.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_ABS),
  /**
   * Floating-point negation.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_NEG),
  /**
   * Floating-point addition.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2..3:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_ADD),
  /**
   * Floating-point sutraction.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2..3:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_SUB),
  /**
   * Floating-point multiply.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2..3:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_MULT),
  /**
   * Floating-point division.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2..3:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_DIV),
  /**
   * Floating-point fused multiply and add.
   *
   * - Arity: ``4``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2..4:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_FMA),
  /**
   * Floating-point square root.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_SQRT),
  /**
   * Floating-point remainder.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_REM),
  /**
   * Floating-point round to integral.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_RTI),
  /**
   * Floating-point minimum.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_MIN),
  /**
   * Floating-point maximum.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_MAX),
  /**
   * Floating-point less than or equal.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_LEQ),
  /**
   * Floating-point less than.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_LT),
  /**
   * Floating-point greater than or equal.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_GEQ),
  /**
   * Floating-point greater than.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of floating-point Sort (sorts must match)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_GT),
  /**
   * Floating-point is normal tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_NORMAL),
  /**
   * Floating-point is sub-normal tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_SUBNORMAL),
  /**
   * Floating-point is zero tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_ZERO),
  /**
   * Floating-point is infinite tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_INF),
  /**
   * Floating-point is NaN tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_NAN),
  /**
   * Floating-point is negative tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_NEG),
  /**
   * Floating-point is positive tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of floating-point Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_IS_POS),
  /**
   * Conversion to floating-point from IEEE-754 bit-vector.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bit-vector Sort
   *
   * - Indices: ``2``
   *
   *   - ``1:`` The exponent size
   *   - ``2:`` The significand size
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_FP_FROM_IEEE_BV),
  /**
   * Conversion to floating-point from floating-point.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of floating-point Sort
   *
   * - Indices: ``2``
   *
   *   - ``1:`` The exponent size
   *   - ``2:`` The significand size
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_FP_FROM_FP),
  /**
   * Conversion to floating-point from Real.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of Sort Real
   *
   * - Indices: ``2``
   *
   *   - ``1:`` The exponent size
   *   - ``2:`` The significand size
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_FP_FROM_REAL),
  /**
   * Conversion to floating-point from signed bit-vector.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of bit-vector Sort
   *
   * - Indices: ``2``
   *
   *   - ``1:`` The exponent size
   *   - ``2:`` The significand size
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_FP_FROM_SBV),
  /**
   * Conversion to floating-point from unsigned bit-vector.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of bit-vector Sort
   *
   * - Indices: ``2``
   *
   *   - ``1:`` The exponent size
   *   - ``2:`` The significand size
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_FP_FROM_UBV),
  /**
   * Conversion to unsigned bit-vector from floating-point.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of floating-point Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The size of the bit-vector to convert to.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_UBV),
  /**
   * Conversion to signed bit-vector from floating-point.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort RoundingMode
   *   - ``2:`` Term of floating-point Sort
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The size of the bit-vector to convert to.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_SBV),
  /**
   * Conversion to Real from floating-point.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Real
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FLOATINGPOINT_TO_REAL),

  /* Arrays ---------------------------------------------------------------- */

  /**
   * Array select.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of array Sort
   *   - ``2:`` Term of array index Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SELECT),
  /**
   * Array store.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of array Sort
   *   - ``2:`` Term of array index Sort
   *   - ``3:`` Term of array element Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STORE),
  /**
   * Constant array.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of array Sort
   *   - ``2:`` Term of array element Sort (value)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(CONST_ARRAY),
  /**
   * \rst
   * Equality over arrays :math:`a` and :math:`b` over a given range
   * :math:`[i,j]`, i.e.,
   *
   * .. math::
   *
   *   \forall k . i \leq k \leq j \Rightarrow a[k] = b[k]
   *
   * \endrst
   *
   * - Arity: ``4``
   *
   *   - ``1:`` Term of array Sort (first array)
   *   - ``2:`` Term of array Sort (second array)
   *   - ``3:`` Term of array index Sort (lower bound of range, inclusive)
   *   - ``4:`` Term of array index Sort (upper bound of range, inclusive)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   *
   * .. note:: We currently support the creation of array equalities over index
   *           Sorts bit-vector, floating-point, Int and Real.
   *           Requires to enable option
   *           :ref:`arrays-exp<lbl-option-arrays-exp>`.
   * \endrst
   */
  EVALUE(EQ_RANGE),

  /* Datatypes ------------------------------------------------------------- */

  /**
   * Datatype constructor application.
   *
   * - Arity: ``n > 0``
   *
   *   - ``1:`` DatatypeConstructor Term (see DatatypeConstructor::getTerm() const)
   *   - ``2..n:`` Terms of the Sorts of the selectors of the constructor (the arguments to the constructor)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(APPLY_CONSTRUCTOR),
  /**
   * Datatype selector application.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` DatatypeSelector Term (see DatatypeSelector::getTerm() const)
   *   - ``2:`` Term of the codomain Sort of the selector
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. note:: Undefined if misapplied.
   * \endrst
   */
  EVALUE(APPLY_SELECTOR),
  /**
   * Datatype tester application.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Datatype tester Term (see DatatypeConstructor::getTesterTerm() const)
   *   - ``2:`` Term of Datatype Sort (DatatypeConstructor must belong to this Datatype Sort)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(APPLY_TESTER),
  /**
   * Datatype update application.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Datatype updater Term (see DatatypeSelector::getUpdaterTerm() const)
   *   - ``2:`` Term of Datatype Sort (DatatypeSelector of the updater must belong to a constructor of this Datatype Sort)
   *   - ``3:`` Term of the codomain Sort of the selector (the Term to update the field of the datatype term with)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. note:: Does not change the datatype argument if misapplied.
   * \endrst
   */
  EVALUE(APPLY_UPDATER),
  /**
   * Match expression.
   *
   * This kind is primarily used in the parser to support the
   * SMT-LIBv2 ``match`` expression.
   *
   * For example, the SMT-LIBv2 syntax for the following match term
   * \rst
   * .. code:: smtlib
   *
   *      (match l (((cons h t) h) (nil 0)))
   *
   * is represented by the AST
   *
   * .. code:: lisp
   *
   *     (MATCH l
   *         (MATCH_BIND_CASE (VARIABLE_LIST h t) (cons h t) h)
   *         (MATCH_CASE nil 0))
   *
   * Terms of kind :cpp:enumerator:`MATCH_CASE` are constant case expressions,
   * which are used for nullary constructors. Kind
   * :cpp:enumerator:`MATCH_BIND_CASE` is used for constructors with selectors
   * and variable match patterns. If not all constructors are covered, at least
   * one catch-all variable pattern must be included.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of kind :cpp:enumerator:`MATCH_CASE` and :cpp:enumerator:`MATCH_BIND_CASE`
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(MATCH),
  /**
   * Match case for nullary constructors.
   *
   * A (constant) case expression to be used within a match expression.
   *
   * \rst
   * - Arity: ``2``
   *
   *   - ``1:`` Term of kind :cpp:enumerator:`APPLY_CONSTRUCTOR` (the pattern to match against)
   *   - ``2:`` Term of any Sort (the term the match term evaluates to)
   *
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(MATCH_CASE),
  /**
   * Match case with binders, for constructors with selectors and variable
   * patterns.
   *
   * A (non-constant) case expression to be used within a match expression.
   *
   * \rst
   * - Arity: ``3``
   *
   *   - For variable patterns:
   *
   *     - ``1:`` Term of kind :cpp:enumerator:`VARIABLE_LIST` (containing the free variable of the case)
   *     - ``2:`` Term of kind :cpp:enumerator:`VARIABLE` (the pattern expression, the free variable of the case)
   *     - ``3:`` Term of any Sort (the term the pattern evaluates to)
   *
   *   - For constructors with selectors:
   *
   *     - ``1:`` Term of kind :cpp:enumerator:`VARIABLE_LIST` (containing the free variable of the case)
   *     - ``2:`` Term of kind :cpp:enumerator:`APPLY_CONSTRUCTOR` (the pattern expression, applying the set of variables to the constructor)
   *     - ``3:`` Term of any Sort (the term the match term evaluates to)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(MATCH_BIND_CASE),
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
   *     ((_ tuple.project 1 2 2 3 1) (tuple 10 20 30 40))
   * \endrst
   * yields
   * \rst
   * .. code:: smtlib
   *
   *     (tuple 20 30 30 40 20)
   * \endrst
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of tuple Sort
   *
   * - Indices: ``n``
   *
   *   - ``1..n:`` The tuple indices to project
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(TUPLE_PROJECT),
  /**
   * Lifting operator for nullable terms.
   * This operator lifts a built-in operator or a user-defined function 
   * to nullable terms.
   * For built-in kinds use mkNullableLift.
   * For user-defined functions use mkTerm.
   * 
   * - Arity: ``n > 1``
   *
   * - ``1..n:`` Terms of nullable sort
   *
   * - Create Term of this Kind with:
   *   - Solver::mkNullableLift(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
  */
  EVALUE(NULLABLE_LIFT),
  /* Separation Logic ------------------------------------------------------ */

  /**
   * Separation logic nil.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkSepNil(const Sort&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SEP_NIL),
  /**
   * Separation logic empty heap.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkSepEmp() const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SEP_EMP),
  /**
   * Separation logic points-to relation.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term denoting the location of the points-to constraint
   *   - ``2:`` Term denoting the data of the points-to constraint
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SEP_PTO),
  /**
   * Separation logic star.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of sort Bool (the child constraints that hold in
   *               disjoint (separated) heaps)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SEP_STAR),
  /**
   * Separation logic magic wand.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Terms of Sort Bool (the antecendant of the magic wand constraint)
   *   - ``2:`` Terms of Sort Bool (conclusion of the magic wand constraint,
   *          which is asserted to hold in all heaps that are disjoint
   *          extensions of the antecedent)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SEP_WAND),

  /* Sets ------------------------------------------------------------------ */

  /**
   * Empty set.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkEmptySet(const Sort&) const
   */
  EVALUE(SET_EMPTY),
  /**
   * Set union.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_UNION),
  /**
   * Set intersection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_INTER),
  /**
   * Set subtraction.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_MINUS),
  /**
   * Subset predicate.
   *
   * Determines if the first set is a subset of the second set.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_SUBSET),
  /**
   * Set membership predicate.
   *
   * Determines if the given set element is a member of the second set.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of any Sort (must match the element Sort of the given set Term)
   *   - ``2:`` Term of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_MEMBER),
  /**
   * Singleton set.
   *
   * Construct a singleton set from an element given as a parameter.
   * The returned set has the same Sort as the element.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of any Sort (the set element)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_SINGLETON),
  /**
   * The set obtained by inserting elements;
   *
   * - Arity: ``n > 0``
   *
   *   - ``1..n-1:`` Terms of any Sort (must match the element sort of the given set Term)
   *   - ``n:`` Term of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_INSERT),
  /**
   * Set cardinality.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_CARD),
  /**
   * Set complement with respect to finite universe.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SET_COMPLEMENT),
  /**
   * Finite universe set.
   *
   * All set variables must be interpreted as subsets of it.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkUniverseSet(const Sort&) const
   *
   * \rst
   * .. note:: :cpp:enumerator:`SET_UNIVERSE` is considered a special symbol of
   *           the theory of sets and is not considered as a set value, i.e.,
   *           Term::isSetValue() will return ``false``.
   * \endrst
   */
  EVALUE(SET_UNIVERSE),
  /**
   * Set comprehension
   *
   * \rst
   * A set comprehension is specified by a variable list :math:`x_1 ... x_n`,
   * a predicate :math:`P[x_1...x_n]`, and a term :math:`t[x_1...x_n]`. A
   * comprehension :math:`C` with the above form has members given by the
   * following semantics:
   *
   * .. math::
   *
   *  \forall y. ( \exists x_1...x_n. P[x_1...x_n] \wedge t[x_1...x_n] = y )
   *  \Leftrightarrow (set.member \; y \; C)
   *
   * where :math:`y` ranges over the element Sort of the (set) Sort of the
   * comprehension. If :math:`t[x_1..x_n]` is not provided, it is equivalent
   * to :math:`y` in the above formula.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Kind :cpp:enumerator:`VARIABLE_LIST`
   *   - ``2:`` Term of sort Bool (the predicate of the comprehension)
   *   - ``3:`` (optional) Term denoting the generator for the comprehension
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SET_COMPREHENSION),
  /**
   * Set choose.
   *
   * \rst
   * Select an element from a given set. For a set :math:`A = \{x\}`, the term
   * (set.choose :math:`A`) is equivalent to the term :math:`x_1`. For an empty
   * set, it is an arbitrary value. For a set with cardinality > 1, it will
   * deterministically return an element in :math:`A`.
   * \endrst
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SET_CHOOSE),
  /**
   * Set is singleton tester.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of set Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SET_IS_SINGLETON),
  /**
   * Set map.
   *
   * \rst
   * This operator applies the first argument, a function of
   * Sort :math:`(\rightarrow S_1 \; S_2)`, to every element of the second
   * argument, a set of Sort (Set :math:`S_1`), and returns a set of Sort
   * (Set :math:`S_2`).
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow S_1 \; S_2)`
   *   - ``2:`` Term of set Sort (Set :math:`S_1`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
   EVALUE(SET_MAP),
  /**
   * Set filter.
   *
   * \rst
   * This operator filters the elements of a set.
   * (set.filter :math:`p \; A`) takes a predicate :math:`p` of Sort
   * :math:`(\rightarrow T \; Bool)` as a first argument, and a set :math:`A`
   * of Sort (Set :math:`T`) as a second argument, and returns a subset of Sort
   * (Set :math:`T`) that includes all elements of :math:`A` that satisfy
   * :math:`p`.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow T \; Bool)`
   *   - ``2:`` Term of bag Sort (Set :math:`T`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
   EVALUE(SET_FILTER),
   /**
   * Set fold.
   *
   * \rst
   * This operator combines elements of a set into a single value.
   * (set.fold :math:`f \; t \; A`) folds the elements of set :math:`A`
   * starting with Term :math:`t` and using the combining function :math:`f`.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow S_1 \; S_2 \; S_2)`
   *   - ``2:`` Term of Sort :math:`S_2` (the initial value)
   *   - ``3:`` Term of bag Sort (Set :math:`S_1`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(SET_FOLD),

  /* Relations ------------------------------------------------------------- */

  /**
   * Relation join.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of relation Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(RELATION_JOIN),
  /**
   * Relation cartesian product.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of relation Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(RELATION_PRODUCT),
  /**
   * Relation transpose.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of relation Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(RELATION_TRANSPOSE),
  /**
   * Relation transitive closure.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of relation Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(RELATION_TCLOSURE),
  /**
   * Relation join image.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of relation Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(RELATION_JOIN_IMAGE),
  /**
   * Relation identity.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of relation Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(RELATION_IDEN),
  /**
   * Relation group
   *
   * \rst
   * :math:`((\_ \; rel.group \; n_1 \; \dots \; n_k) \; A)` partitions tuples
   * of relation :math:`A` such that tuples that have the same projection
   * with indices :math:`n_1 \; \dots \; n_k` are in the same part.
   * It returns a set of relations of type :math:`(Set \; T)` where
   * :math:`T` is the type of :math:`A`.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of relation sort
   *
   * - Indices: ``n``
   *
   *   - ``1..n:``  Indices of the projection
   *
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(RELATION_GROUP),
  /**
   * \rst
   *
   * Relation aggregate operator has the form
   * :math:`((\_ \; rel.aggr \; n_1 ... n_k) \; f \; i \; A)`
   * where :math:`n_1, ..., n_k` are natural numbers,
   * :math:`f` is a function of type
   * :math:`(\rightarrow (Tuple \;  T_1 \; ... \; T_j)\; T \; T)`,
   * :math:`i` has the type :math:`T`,
   * and :math:`A` has type :math:`(Relation \;  T_1 \; ... \; T_j)`.
   * The returned type is :math:`(Set \; T)`.
   *
   * This operator aggregates elements in A that have the same tuple projection
   * with indices n_1, ..., n_k using the combining function :math:`f`,
   * and initial value :math:`i`.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sort :math:`(\rightarrow (Tuple \;  T_1 \; ... \; T_j)\; T \; T)`
   *   - ``2:`` Term of Sort :math:`T`
   *   - ``3:`` Term of relation sort :math:`Relation T_1 ... T_j`
   *
   * - Indices: ``n``
   *   - ``1..n:`` Indices of the projection
   * \endrst
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(RELATION_AGGREGATE),
  /**
   * Relation projection operator extends tuple projection operator to sets.
   *
   * - Arity: ``1``
   *   - ``1:`` Term of relation Sort
   *
   * - Indices: ``n``
   *   - ``1..n:`` Indices of the projection
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(RELATION_PROJECT),

  /* Bags ------------------------------------------------------------------ */

  /**
   * Empty bag.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkEmptyBag(const Sort&) const
   */
  EVALUE(BAG_EMPTY),
  /**
   * Bag max union.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_UNION_MAX),
  /**
   * Bag disjoint union (sum).
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_UNION_DISJOINT),
  /**
   * Bag intersection (min).
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_INTER_MIN),
  /**
   * Bag difference subtract.
   *
   * Subtracts multiplicities of the second from the first.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_DIFFERENCE_SUBTRACT),
  /**
   * Bag difference remove.
   *
   * Removes shared elements in the two bags.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_DIFFERENCE_REMOVE),
  /**
   * Bag inclusion predicate.
   *
   * Determine if multiplicities of the first bag are less than or equal to
   * multiplicities of the second bag.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_SUBBAG),
  /**
   * Bag element multiplicity.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const Term&, const Term&) const
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   */
  EVALUE(BAG_COUNT),
  /**
   * Bag membership predicate.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of any Sort (must match the element Sort of the given bag Term)
   *   - ``2:`` Terms of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_MEMBER),
  /**
   * Bag setof.
   *
   * Eliminate duplicates in a given bag. The returned bag contains exactly the
   * same elements in the given bag, but with multiplicity one.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(BAG_SETOF),
  /**
   * Bag make.
   *
   * Construct a bag with the given element and given multiplicity.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of any Sort (the bag element)
   *   - ``2:`` Term of Sort Int (the multiplicity of the element)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(BAG_MAKE),
  /**
   * Bag cardinality.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(BAG_CARD),
  /**
   * Bag choose.
   *
   * Select an element from a given bag.
   *
   * \rst
   * For a bag :math:`A = \{(x,n)\}` where :math:`n` is the multiplicity, then
   * the term (choose :math:`A`) is equivalent to the term :math:`x`. For an
   * empty bag, then it is an arbitrary value. For a bag that contains distinct
   * elements, it will deterministically return an element in :math:`A`.
   * \endrst
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of bag Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(BAG_CHOOSE),  
  /**
   * Bag map.
   *
   * \rst
   * This operator applies the first argument, a function of
   * Sort :math:`(\rightarrow S_1 \; S_2)`, to every element of the second
   * argument, a set of Sort (Bag :math:`S_1`), and returns a set of Sort
   * (Bag :math:`S_2`).
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow S_1 \; S_2)`
   *   - ``2:`` Term of bag Sort (Bag :math:`S_1`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(BAG_MAP),
  /**
   * Bag filter.
   *
   * \rst
   * This operator filters the elements of a bag.
   * (bag.filter :math:`p \; B`) takes a predicate :math:`p` of Sort
   * :math:`(\rightarrow T \; Bool)` as a first argument, and a bag :math:`B`
   * of Sort (Bag :math:`T`) as a second argument, and returns a subbag of Sort
   * (Bag :math:`T`) that includes all elements of :math:`B` that satisfy
   * :math:`p` with the same multiplicity.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow T \; Bool)`
   *   - ``2:`` Term of bag Sort (Bag :math:`T`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
   EVALUE(BAG_FILTER),
  /**
   * Bag fold.
   *
   * \rst
   * This operator combines elements of a bag into a single value.
   * (bag.fold :math:`f \; t \; B`) folds the elements of bag :math:`B`
   * starting with Term :math:`t` and using the combining function :math:`f`.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow S_1 \; S_2 \; S_2)`
   *   - ``2:`` Term of Sort :math:`S_2` (the initial value)
   *   - ``3:`` Term of bag Sort (Bag :math:`S_1`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(BAG_FOLD),
  /**
   * Bag partition.
   *
   * \rst
   * This operator partitions of a bag of elements into disjoint bags.
   * (bag.partition :math:`r \; B`) partitions the elements of bag :math:`B`
   * of type :math:`(Bag \; E)` based on the equivalence relations :math:`r` of
   * type :math:`(\rightarrow \; E \; E \; Bool)`.
   * It returns a bag of bags of type :math:`(Bag \; (Bag \; E))`.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of function Sort :math:`(\rightarrow \; E \; E \; Bool)`
   *   - ``2:`` Term of bag Sort (Bag :math:`E`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(BAG_PARTITION),
  /**
   * Table cross product.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of table Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(TABLE_PRODUCT),
  /**
   * Table projection operator extends tuple projection operator to tables.
   *
   * - Arity: ``1``
   *   - ``1:`` Term of table Sort
   *
   * - Indices: ``n``
   *   - ``1..n:`` Indices of the projection
   *
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(TABLE_PROJECT),
  /**
   * \rst
   *
   * Table aggregate operator has the form
   * :math:`((\_ \; table.aggr \; n_1 ... n_k) \; f \; i \; A)`
   * where :math:`n_1, ..., n_k` are natural numbers,
   * :math:`f` is a function of type
   * :math:`(\rightarrow (Tuple \;  T_1 \; ... \; T_j)\; T \; T)`,
   * :math:`i` has the type :math:`T`,
   * and :math:`A` has type :math:`(Table \;  T_1 \; ... \; T_j)`.
   * The returned type is :math:`(Bag \; T)`.
   *
   * This operator aggregates elements in A that have the same tuple projection
   * with indices n_1, ..., n_k using the combining function :math:`f`,
   * and initial value :math:`i`.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sort :math:`(\rightarrow (Tuple \;  T_1 \; ... \; T_j)\; T \; T)`
   *   - ``2:`` Term of Sort :math:`T`
   *   - ``3:`` Term of table sort :math:`Table T_1 ... T_j`
   *
   * - Indices: ``n``
   *   - ``1..n:`` Indices of the projection
   * \endrst
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(TABLE_AGGREGATE),
  /**
   * \rst
   *  Table join operator has the form
   *  :math:`((\_ \; table.join \; m_1 \; n_1 \; \dots \; m_k \; n_k) \; A \; B)`
   *  where :math:`m_1 \; n_1 \; \dots \; m_k \; n_k` are natural numbers,
   *  and :math:`A, B` are tables.
   *  This operator filters the product of two bags based on the equality of
   *  projected tuples using indices :math:`m_1, \dots, m_k` in table :math:`A`,
   *  and indices :math:`n_1, \dots, n_k` in table :math:`B`.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of table Sort
   *
   *   - ``2:`` Term of table Sort
   *
   * - Indices: ``n``
   *   - ``1..n:``  Indices of the projection
   *
   * \endrst
   * - Create Term of this Kind with:
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(TABLE_JOIN),
  /**
   * Table group
   *
   * \rst
   * :math:`((\_ \; table.group \; n_1 \; \dots \; n_k) \; A)` partitions tuples
   * of table :math:`A` such that tuples that have the same projection
   * with indices :math:`n_1 \; \dots \; n_k` are in the same part.
   * It returns a bag of tables of type :math:`(Bag \; T)` where
   * :math:`T` is the type of :math:`A`.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of table sort
   *
   * - Indices: ``n``
   *
   *   - ``1..n:``  Indices of the projection
   *
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   * \endrst
   */
  EVALUE(TABLE_GROUP),

  /* Strings --------------------------------------------------------------- */

  /**
   * String concat.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_CONCAT),
  /**
   * String membership.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String
   *   - ``2:`` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_IN_REGEXP),
  /**
   * String length.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_LENGTH),
  /**
   * String substring.
   *
   * \rst
   * Extracts a substring, starting at index :math:`i` and of length :math:`l`,
   * from a string :math:`s`.  If the start index is negative, the start index
   * is greater than the length of the string, or the length is negative, the
   * result is the empty string.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String
   *   - ``2:`` Term of Sort Int (index :math:`i`)
   *   - ``3:`` Term of Sort Int (length :math:`l`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_SUBSTR),
  /**
   * String update.
   *
   * \rst
   * Updates a string :math:`s` by replacing its context starting at an index
   * with string :math:`t`. If the start index is negative, the start index is
   * greater than the length of the string, the result is :math:`s`. Otherwise,
   * the length of the original string is preserved.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String
   *   - ``2:`` Term of Sort Int (index :math:`i`)
   *   - ``3:`` Term of Sort Strong (replacement string :math:`t`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_UPDATE),
  /**
   * String character at.
   *
   * \rst
   * Returns the character at index :math:`i` from a string :math:`s`. If the
   * index is negative or the index is greater than the length of the string,
   * the result is the empty string. Otherwise the result is a string of
   * length 1.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (string :math:`s`)
   *   - ``2:`` Term of Sort Int (index :math:`i`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_CHARAT),
  /**
   * String contains.
   *
   * \rst
   * Determines whether a string :math:`s_1` contains another string
   * :math:`s_2`. If :math:`s_2` is empty, the result is always ``true``.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (the string :math:`s_1`)
   *   - ``2:`` Term of Sort String (the string :math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_CONTAINS),
  /**
   * String index-of.
   *
   * \rst
   * Returns the index of a substring :math:`s_2` in a string :math:`s_1`
   * starting at index :math:`i`. If the index is negative or greater than the
   * length of string :math:`s_1` or the substring :math:`s_2` does not appear
   * in string :math:`s_1` after index :math:`i`, the result is -1.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (substring :math:`s_1`)
   *   - ``2:`` Term of Sort String (substring :math:`s_2`)
   *   - ``3:`` Term of Sort Int (index :math:`i`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_INDEXOF),
  /**
   * String index-of regular expression match.
   *
   * \rst
   * Returns the first match of a regular expression :math:`r` in a
   * string :math:`s`. If the index is negative or greater than the length of
   * string :math:`s_1`, or :math:`r` does not match a substring in :math:`s`
   * after index :math:`i`, the result is -1.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String (string :math:`s`)
   *   - ``2:`` Term of Sort RegLan (regular expression :math:`r`)
   *   - ``3:`` Term of Sort Int (index :math:`i`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_INDEXOF_RE),
  /**
   * String replace.
   *
   * \rst
   * Replaces a string :math:`s_2` in a string :math:`s_1` with string
   * :math:`s_3`. If :math:`s_2` does not appear in :math:`s_1`, :math:`s_1` is
   * returned unmodified.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String (string :math:`s_1`)
   *   - ``2:`` Term of Sort String (string :math:`s_2`)
   *   - ``3:`` Term of Sort String (string :math:`s_3`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_REPLACE),
  /**
   * String replace all.
   *
   * \rst
   * Replaces all occurrences of a string :math:`s_2` in a string :math:`s_1`
   * with string :math:`s_3`. If :math:`s_2` does not appear in :math:`s_1`,
   * :math:`s_1` is returned unmodified.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort String (:math:`s_2`)
   *   - ``3:`` Term of Sort String (:math:`s_3`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_REPLACE_ALL),
  /**
   * String replace regular expression match.
   *
   * \rst
   * Replaces the first match of a regular expression :math:`r` in
   * string :math:`s_1` with string :math:`s_2`. If :math:`r` does not match a
   * substring of :math:`s_1`, :math:`s_1` is returned unmodified.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort RegLan
   *   - ``3:`` Term of Sort String (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_REPLACE_RE),
  /**
   * String replace all regular expression matches.
   *
   * \rst
   * Replaces all matches of a regular expression :math:`r` in string
   * :math:`s_1` with string :math:`s_2`. If :math:`r` does not match a
   * substring of :math:`s_1`, string :math:`s_1` is returned unmodified.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort RegLan
   *   - ``3:`` Term of Sort String (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_REPLACE_RE_ALL),
  /**
   * String to lower case.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_TO_LOWER),
  /**
   * String to upper case.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_TO_UPPER),
  /**
   * String reverse.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_REV),
  /**
   * String to code.
   *
   * Returns the code point of a string if it has length one, or returns `-1`
   * otherwise.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_TO_CODE),
  /**
   * String from code.
   *
   * Returns a string containing a single character whose code point matches
   * the argument to this function, or the empty string if the argument is
   * out-of-bounds.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_FROM_CODE),
  /**
   * String less than.
   *
   * \rst
   * Returns true if string :math:`s_1` is (strictly) less than :math:`s_2`
   * based on a lexiographic ordering over code points.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort String (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_LT),
  /**
   * String less than or equal.
   *
   * \rst
   * Returns true if string :math:`s_1` is less than or equal to :math:`s_2`
   * based on a lexiographic ordering over code points.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort String (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_LEQ),
  /**
   * String prefix-of.
   *
   * \rst
   * Determines whether a string :math:`s_1` is a prefix of string :math:`s_2`.
   * If string s1 is empty, this operator returns ``true``.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort String (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_PREFIX),
  /**
   * String suffix-of.
   *
   * \rst
   * Determines whether a string :math:`s_1` is a suffix of the second string.
   * If string :math:`s_1` is empty, this operator returns ``true``.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (:math:`s_1`)
   *   - ``2:`` Term of Sort String (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_SUFFIX),
  /**
   * String is-digit.
   *
   * Returns true if given string is a digit (it is one of ``"0"``, ...,
   * ``"9"``).
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_IS_DIGIT),
  /**
   * Conversion from Int to String.
   *
   * If the integer is negative this operator returns the empty string.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_FROM_INT),
  /**
   * String to integer (total function).
   *
   * If the string does not contain an integer or the integer is negative, the
   * operator returns `-1`.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort Int
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_TO_INT),
  /**
   * Constant string.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkString(const std::string&, bool) const
   *   - Solver::mkString(const std::wstring&) const
   */
  EVALUE(CONST_STRING),
  /**
   * Conversion from string to regexp.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort String
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(STRING_TO_REGEXP),
  /**
   * Regular expression concatenation.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_CONCAT),
  /**
   * Regular expression union.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_UNION),
  /**
   * Regular expression intersection.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_INTER),
  /**
   * Regular expression difference.
   *
   * - Arity: ``2``
   *
   *   - ``1..2:`` Terms of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_DIFF),
  /**
   * Regular expression \*.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_STAR),
  /**
   * Regular expression +.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_PLUS),
  /**
   * Regular expression ?.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_OPT),
  /**
   * Regular expression range.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of Sort String (lower bound character for the range)
   *   - ``2:`` Term of Sort String (upper bound character for the range)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_RANGE),
  /**
   * Operator for regular expression repeat.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort RegLan
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The number of repetitions
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_REPEAT),
  /**
   * Regular expression loop.
   *
   * Regular expression loop from lower bound to upper bound number of
   * repetitions.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort RegLan
   *
   * - Indices: ``1``
   *
   *   - ``1:`` The lower bound
   *   - ``2:`` The upper bound
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_LOOP),
  /**
   * Regular expression none.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkRegexpNone() const
   */
  EVALUE(REGEXP_NONE),
  /**
   * Regular expression all.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkRegexpAll() const
   */
  EVALUE(REGEXP_ALL),
  /**
   * Regular expression all characters.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkRegexpAllchar() const
   */
  EVALUE(REGEXP_ALLCHAR),
  /**
   * Regular expression complement.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of Sort RegLan
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(REGEXP_COMPLEMENT),

  /**
   * Sequence concat.
   *
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of sequence Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_CONCAT),
  /**
   * Sequence length.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of sequence Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_LENGTH),
  /**
   * Sequence extract.
   *
   * \rst
   * Extracts a subsequence, starting at index :math:`i` and of length :math:`l`,
   * from a sequence :math:`s`.  If the start index is negative, the start index
   * is greater than the length of the sequence, or the length is negative, the
   * result is the empty sequence.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sequence Sort
   *   - ``2:`` Term of Sort Int (index :math:`i`)
   *   - ``3:`` Term of Sort Int (length :math:`l`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_EXTRACT),
  /**
   * Sequence update.
   *
   * \rst
   * Updates a sequence :math:`s` by replacing its context starting at an index
   * with string :math:`t`. If the start index is negative, the start index is
   * greater than the length of the sequence, the result is :math:`s`.
   * Otherwise, the length of the original sequence is preserved.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sequence Sort
   *   - ``2:`` Term of Sort Int (index :math:`i`)
   *   - ``3:`` Term of sequence Sort (replacement sequence :math:`t`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_UPDATE),
  /**
   * Sequence element at.
   *
   * \rst
   * Returns the element at index :math:`i` from a sequence :math:`s`. If the index
   * is negative or the index is greater or equal to the length of the
   * sequence, the result is the empty sequence. Otherwise the result is a
   * sequence of length ``1``.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of sequence Sort
   *   - ``2:`` Term of Sort Int (index :math:`i`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_AT),
  /**
   * Sequence contains.
   *
   * \rst
   * Checks whether a sequence :math:`s_1` contains another sequence
   * :math:`s_2`. If :math:`s_2` is empty, the result is always ``true``.
   *
   * - Arity: ``2``
   *
   *   - ``1:`` Term of sequence Sort (:math:`s_1`)
   *   - ``2:`` Term of sequence Sort (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_CONTAINS),
  /**
   * Sequence index-of.
   *
   * \rst
   * Returns the index of a subsequence :math:`s_2` in a sequence :math:`s_1`
   * starting at index :math:`i`. If the index is negative or greater than the
   * length of sequence :math:`s_1` or the subsequence :math:`s_2` does not
   * appear in sequence :math:`s_1` after index :math:`i`, the result is -1.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sequence Sort (:math:`s_1`)
   *   - ``2:`` Term of sequence Sort (:math:`s_2`)
   *   - ``3:`` Term of Sort Int (:math:`i`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_INDEXOF),
  /**
   * Sequence replace.
   *
   * \rst
   * Replaces the first occurrence of a sequence :math:`s_2` in a
   * sequence :math:`s_1` with sequence :math:`s_3`. If :math:`s_2` does not
   * appear in :math:`s_1`, :math:`s_1` is returned unmodified.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sequence Sort (:math:`s_1`)
   *   - ``2:`` Term of sequence Sort (:math:`s_2`)
   *   - ``3:`` Term of sequence Sort (:math:`s_3`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_REPLACE),
  /**
   * Sequence replace all.
   *
   * \rst
   * Replaces all occurrences of a sequence :math:`s_2` in a sequence
   * :math:`s_1` with sequence :math:`s_3`. If :math:`s_2` does not appear in
   * :math:`s_1`, sequence :math:`s_1` is returned unmodified.
   *
   * - Arity: ``3``
   *
   *   - ``1:`` Term of sequence Sort (:math:`s_1`)
   *   - ``2:`` Term of sequence Sort (:math:`s_2`)
   *   - ``3:`` Term of sequence Sort (:math:`s_3`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_REPLACE_ALL),
  /**
   * Sequence reverse.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of sequence Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_REV),
  /**
   * Sequence prefix-of.
   *
   * \rst
   * Checks whether a sequence :math:`s_1` is a prefix of sequence :math:`s_2`.
   * If sequence :math:`s_1` is empty, this operator returns ``true``.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of sequence Sort (:math:`s_1`)
   *   - ``2:`` Term of sequence Sort (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_PREFIX),
  /**
   * Sequence suffix-of.
   *
   * \rst
   * Checks whether a sequence :math:`s_1` is a suffix of sequence :math:`s_2`.
   * If sequence :math:`s_1` is empty, this operator returns ``true``.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of sequence Sort (:math:`s_1`)
   *   - ``2:`` Term of sequence Sort (:math:`s_2`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_SUFFIX),
  /**
   * Constant sequence.
   *
   * A constant sequence is a term that is equivalent to:
   * \rst
   * .. code:: smtlib
   *
   *     (seq.++ (seq.unit c1) ... (seq.unit cn))
   *
   * where :math:`n \leq 0` and :math:`c_1, ..., c_n` are constants of some
   * sort. The elements can be extracted with Term::getSequenceValue().
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkEmptySequence(const Sort&) const
   */
  EVALUE(CONST_SEQUENCE),
  /**
   * Sequence unit.
   *
   * Corresponds to a sequence of length one with the given term.
   *
   * - Arity: ``1``
   *
   *   - ``1:`` Term of any Sort (the element term)
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_UNIT),
  /**
   * Sequence nth.
   *
   * Corresponds to the nth element of a sequence.
   *
   * \rst
   * - Arity: ``2``
   *
   *   - ``1:`` Term of sequence Sort
   *   - ``2:`` Term of Sort Int (:math:`n`)
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(SEQ_NTH),

  /* Quantifiers ----------------------------------------------------------- */

  /**
   * Universally quantified formula.
   *
   * \rst
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Kind :cpp:enumerator:`VARIABLE_LIST`
   *   - ``2:`` Term of Sort Bool (the quantifier body)
   *   - ``3:`` (optional) Term of Kind :cpp:enumerator:`INST_PATTERN`
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(FORALL),
  /**
   * Existentially quantified formula.
   *
   * \rst
   * - Arity: ``3``
   *
   *   - ``1:`` Term of Kind :cpp:enumerator:`VARIABLE_LIST`
   *   - ``2:`` Term of Sort Bool (the quantifier body)
   *   - ``3:`` (optional) Term of Kind :cpp:enumerator:`INST_PATTERN`
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(EXISTS),
  /**
   * Variable list.
   *
   * A list of variables (used to bind variables under a quantifier)
   *
   * \rst
   * - Arity: ``n > 0``
   *
   *   - ``1..n:`` Terms of Kind :cpp:enumerator:`VARIABLE`
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(VARIABLE_LIST),
  /**
   * Instantiation pattern.
   *
   * Specifies a (list of) terms to be used as a pattern for quantifier
   * instantiation.
   *
   * - Arity: ``n > 0``
   *
   *   - ``1..n:`` Terms of any Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. note:: Should only be used as a child of
   *           :cpp:enumerator:`INST_PATTERN_LIST`.
   * \endrst
   */
  EVALUE(INST_PATTERN),
  /**
   * Instantiation no-pattern.
   *
   * Specifies a (list of) terms that should not be used as a pattern for
   * quantifier instantiation.
   *
   * - Arity: ``n > 0``
   *
   *   - ``1..n:`` Terms of any Sort
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. note:: Should only be used as a child of
   *           :cpp:enumerator:`INST_PATTERN_LIST`.
   * \endrst
   */
  EVALUE(INST_NO_PATTERN),
  /**
   * Instantiation pool annotation.
   *
   * Specifies an annotation for pool based instantiation.
   *
   * In detail, pool symbols can be declared via the method
   *  - Solver::declarePool(const std::string&, const Sort&, const std::vector<Term>&) const
   *
   * A pool symbol represents a set of terms of a given sort. An instantiation
   * pool annotation should either:
   * (1) have child sets matching the types of the quantified formula,
   * (2) have a child set of tuple type whose component types match the types
   * of the quantified formula.
   *
   * For an example of (1), for a quantified formula:
   *
   * \rst
   * .. code:: lisp
   *
   *     (FORALL (VARIABLE_LIST x y) F (INST_PATTERN_LIST (INST_POOL p q)))
   *
   * if :math:`x` and :math:`y` have Sorts :math:`S_1` and :math:`S_2`, then
   * pool symbols :math:`p` and :math:`q` should have Sorts (Set :math:`S_1`)
   * and (Set :math:`S_2`), respectively. This annotation specifies that the
   * quantified formula above should be instantiated with the product of all
   * terms that occur in the sets :math:`p` and :math:`q`.
   * \endrst
   *
   * Alternatively, as an example of (2), for a quantified formula:
   *
   * \rst
   * .. code:: lisp
   *
   *     (FORALL (VARIABLE_LIST x y) F (INST_PATTERN_LIST (INST_POOL s)))
   *
   * :math:`s` should have Sort (Set (Tuple :math:`S_1` :math:`S_2`)). This
   * annotation specifies that the quantified formula above should be
   * instantiated with the pairs of values in :math:`s`.
   *
   * - Arity: ``n > 0``
   *
   *   - ``1..n:`` Terms that comprise the pools, which are one-to-one with the variables of the quantified formula to be instantiated
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   *
   * .. note:: Should only be used as a child of
   *           :cpp:enumerator:`INST_PATTERN_LIST`.
   * \endrst
   */
  EVALUE(INST_POOL),
  /**
   * A instantantiation-add-to-pool annotation.
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
   *
   * where assume that :math:`x` has type Int. When this quantified formula is
   * instantiated with, e.g., the term :math:`t`, the term ``(ADD t 1)`` is
   * added to pool :math:`p`.
   * \endrst
   *
   * - Arity: ``2``
   *
   *   - ``1:`` The Term whose free variables are bound by the quantified formula.
   *   - ``2:`` The pool to add to, whose Sort should be a set of elements that match the Sort of the first argument.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   *
   * .. note:: Should only be used as a child of
   *           :cpp:enumerator:`INST_PATTERN_LIST`.
   * \endrst
   */
  EVALUE(INST_ADD_TO_POOL),
  /**
   * A skolemization-add-to-pool annotation.
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
   *
   * where assume that :math:`x` has type Int. When this quantified formula is
   * skolemized, e.g., with :math:`k` of type Int, then the term ``(ADD k 1)``
   * is added to the pool :math:`p`.
   * \endrst
   *
   * - Arity: ``2``
   *
   *   - ``1:`` The Term whose free variables are bound by the quantified formula.
   *   - ``2:`` The pool to add to, whose Sort should be a set of elements that match the Sort of the first argument.
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. warning:: This kind is experimental and may be changed or removed in
   *              future versions.
   *
   * .. note:: Should only be used as a child of
   *           :cpp:enumerator:`INST_PATTERN_LIST`.
   * \endrst
   */
  EVALUE(SKOLEM_ADD_TO_POOL),
  /**
   * Instantiation attribute.
   *
   * Specifies a custom property for a quantified formula given by a
   * term that is ascribed a user attribute.
   *
   * - Arity: ``n > 0``
   *
   *   - ``1:`` Term of Kind :cpp:enumerator:`CONST_STRING` (the keyword of the attribute)
   *   - ``2...n:`` Terms representing the values of the attribute
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   *
   * \rst
   * .. note:: Should only be used as a child of
   *           :cpp:enumerator:`INST_PATTERN_LIST`.
   * \endrst
   */
  EVALUE(INST_ATTRIBUTE),
  /**
   * A list of instantiation patterns, attributes or annotations.
   *
   * \rst
   * - Arity: ``n > 1``
   *
   *   - ``1..n:`` Terms of Kind :cpp:enumerator:`INST_PATTERN`, :cpp:enumerator:`INST_NO_PATTERN`, :cpp:enumerator:`INST_POOL`, :cpp:enumerator:`INST_ADD_TO_POOL`, :cpp:enumerator:`SKOLEM_ADD_TO_POOL`, :cpp:enumerator:`INST_ATTRIBUTE`
   * \endrst
   *
   * - Create Term of this Kind with:
   *
   *   - Solver::mkTerm(Kind, const std::vector<Term>&) const
   *   - Solver::mkTerm(const Op&, const std::vector<Term>&) const
   *
   * - Create Op of this kind with:
   *
   *   - Solver::mkOp(Kind, const std::vector<uint32_t>&) const
   */
  EVALUE(INST_PATTERN_LIST),

  /* ----------------------------------------------------------------------- */
  /** Marks the upper-bound of this enumeration. */
  EVALUE(LAST_KIND)
};
// clang-format on

#ifdef CVC5_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(Kind) ENUM(Kind);
#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS
/**
 * Get a string representation of a Cvc5Kind.
 * @param kind The kind.
 * @return The string representation.
 */
const char* cvc5_kind_to_string(Cvc5Kind kind);
#else
/**
 * Get the string representation of a given kind.
 * @param kind The kind
 * @return The string representation.
 * @warning This function is deprecated and replaced by
 *          `std::to_string(Kind kind)`. It will be removed in a future release.
 */
[[deprecated("use std::to_string(Kind) instead.")]] CVC5_EXPORT std::string
kindToString(Kind kind);
/**
 * Serialize a kind to given stream.
 * @param out  The output stream.
 * @param kind The kind to be serialized to the given output stream.
 * @return The output stream.
 */
CVC5_EXPORT std::ostream& operator<<(std::ostream& out, Kind kind);

}  // namespace cvc5

namespace std {
/**
 * Get the string representation of a given kind.
 * @param kind The kind
 * @return The string representation.
 */
std::string to_string(cvc5::Kind kind);
}
#endif

#ifdef CVC5_API_USE_C_ENUMS
/**
 * Hash function for Cvc5Kinds.
 * @param kind The kind.
 * @return The hash value.
 */
size_t cvc5_kind_hash(Cvc5Kind kind);
#else
namespace std {

/**
 * Hash function for Kinds.
 */
template <>
struct CVC5_EXPORT hash<cvc5::Kind>
{
  /**
   * Hashes a Kind to a size_t.
   * @param kind The kind.
   * @return The hash value.
   */
  size_t operator()(cvc5::Kind kind) const;
};

}  // namespace std
#endif

/* -------------------------------------------------------------------------- */
/* SortKind */
/* -------------------------------------------------------------------------- */

#ifdef CVC5_API_USE_C_ENUMS
#undef EVALUE
#define EVALUE(name) CVC5_SORT_KIND_##name
#endif

#ifndef CVC5_API_USE_C_ENUMS
namespace cvc5 {
#endif

// clang-format off
/**
 * The kind of a cvc5 Sort.
 *
 * \internal
 *
 * Note that the API type `cvc5::SortKind` roughly corresponds to
 * `cvc5::internal::Kind`, but is a different type. It hides internal kinds
 * that should not be exported to the API, and maps all kinds that we want to
 * export to its corresponding internal kinds. The underlying type of
 * `cvc5::Kind` must be signed (to enable range checks for validity). The size
 * of this type depends on the size of `cvc5::internal::Kind`
 * (`NodeValue::NBITS_KIND`, currently 10 bits, see expr/node_value.h).
 */
enum ENUM(SortKind) : int32_t
{
  /**
   * Internal kind.
   *
   * This kind serves as an abstraction for internal kinds that are not exposed
   * via the API but may appear in terms returned by API functions, e.g.,
   * when querying the simplified form of a term.
   *
   * \rst
   * .. note:: Should never be created via the API.
   * \endrst
   */
  EVALUE(INTERNAL_SORT_KIND = -2),
  /**
   * Undefined kind.
   *
   * \rst
   * .. note:: Should never be exposed or created via the API.
   * \endrst
   */
  EVALUE(UNDEFINED_SORT_KIND = -1),
  /**
   * Null kind.
   *
   * The kind of a null sort (Sort::Sort()).
   *
   * \rst
   * .. note:: May not be explicitly created via API functions other than
   *           :cpp:func:`Sort::Sort()`.
   * \endrst
   */
  EVALUE(NULL_SORT),

  /* Sort Kinds ------------------------------------------------------------ */
  /**
   * An abstract sort.
   *
   * An abstract sort represents a sort whose parameters or argument sorts are
   * unspecified. For example, `mkAbstractSort(BITVECTOR_SORT)` returns a
   * sort that represents the sort of bit-vectors whose bit-width is
   * unspecified.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkAbstractSort(SortKind) const
   */
  EVALUE(ABSTRACT_SORT),
  /**
   * An array sort, whose argument sorts are the index and element sorts of the
   * array.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkArraySort(Sort, Sort) const
   */
  EVALUE(ARRAY_SORT),
  /**
   * A bag sort, whose argument sort is the element sort of the bag.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkBagSort(Sort) const
   */
  EVALUE(BAG_SORT),
  /**
   * The Boolean sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getBooleanSort() const
   */
  EVALUE(BOOLEAN_SORT),
  /**
   * A bit-vector sort, parameterized by an integer denoting its bit-width.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkBitVectorSort(uint32_t) const
   */
  EVALUE(BITVECTOR_SORT),
  /**
   * A datatype sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkDatatypeSort(DatatypeDecl)
   *   - Solver::mkDatatypeSorts(const std::vector<DatatypeDecl>&)
   */
  EVALUE(DATATYPE_SORT),
  /**
   * A finite field sort, parameterized by a size.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkFiniteFieldSort(const std::string&, uint32_t base) const
   */
  EVALUE(FINITE_FIELD_SORT),
  /**
   * A floating-point sort, parameterized by two integers denoting its
   * exponent and significand bit-widths.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkFloatingPointSort(uint32_t, uint32_t) const
   */
  EVALUE(FLOATINGPOINT_SORT),
  /**
   * A function sort with given domain sorts and codomain sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkFunctionSort(const std::vector<Sort>&, Sort) const
   */
  EVALUE(FUNCTION_SORT),
  /**
   * The integer sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getIntegerSort() const
   */
  EVALUE(INTEGER_SORT),
  /**
   * The real sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getRealSort() const
   */
  EVALUE(REAL_SORT),
  /**
   * The regular language sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getRegExpSort() const
   */
  EVALUE(REGLAN_SORT),
  /**
   * The rounding mode sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getRoundingModeSort() const
   */
  EVALUE(ROUNDINGMODE_SORT),
  /**
   * A sequence sort, whose argument sort is the element sort of the sequence.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkSequenceSort(Sort) const
   */
  EVALUE(SEQUENCE_SORT),
  /**
   * A set sort, whose argument sort is the element sort of the set.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkSetSort(Sort) const
   */
  EVALUE(SET_SORT),
  /**
   * The string sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::getStringSort() const
   */
  EVALUE(STRING_SORT),
  /**
   * A tuple sort, whose argument sorts denote the sorts of the direct children
   * of the tuple.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkTupleSort(const std::vector<Sort>&) const
   */
  EVALUE(TUPLE_SORT),
  /**
   * A nullable sort, whose argument sort denotes the sort of the direct child
   * of the nullable.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkNullableSort(const Sort&) const
   */
  EVALUE(NULLABLE_SORT),
  /**
   * An uninterpreted sort.
   *
   * - Create Sort of this Kind with:
   *
   *   - Solver::mkUninterpretedSort(const std::optional<std::string>&) const
   */
  EVALUE(UNINTERPRETED_SORT),
  /* ----------------------------------------------------------------------- */
  /** Marks the upper-bound of this enumeration. */
  EVALUE(LAST_SORT_KIND)
};
// clang-format on

#ifdef CVC5_API_USE_C_ENUMS
#ifndef DOXYGEN_SKIP
typedef enum ENUM(SortKind) ENUM(SortKind);
#endif
#endif

#ifdef CVC5_API_USE_C_ENUMS
/**
 * Get a string representation of a Cvc5SortKind.
 * @param kind The sort kind.
 * @return The string representation.
 */
const char* cvc5_sort_kind_to_string(Cvc5SortKind kind);
#else
/**
 * Get the string representation of a given kind.
 * @param k the sort kind
 * @return the string representation of kind k
 * @warning This function is deprecated and replaced by
 *          `std::to_string(SortKind kind)`. It will be removed in a future
 *          release.
 */
[[deprecated("use std::to_string(SortKind) instead.")]] CVC5_EXPORT std::string
sortKindToString(SortKind k);
/**
 * Serialize a kind to given stream.
 * @param out the output stream
 * @param k the sort kind to be serialized to the given output stream
 * @return the output stream
 */
CVC5_EXPORT std::ostream& operator<<(std::ostream& out, SortKind k);

}  // namespace cvc5

namespace std {
/**
 * Get the string representation of a given kind.
 * @param k the sort kind
 * @return the string representation of kind k
 */
std::string to_string(cvc5::SortKind k);
}
#endif

#ifdef CVC5_API_USE_C_ENUMS
/**
 * Hash function for Cvc5SortKinds.
 * @param kind The kind.
 * @return The hash value.
 */
size_t cvc5_sort_kind_hash(Cvc5SortKind kind);
#else
namespace std {

/**
 * Hash function for SortKinds.
 */
template <>
struct CVC5_EXPORT hash<cvc5::SortKind>
{
  /**
   * Hashes a SortKind to a size_t.
   * @param kind The kind.
   * @return The hash value.
   */
  size_t operator()(cvc5::SortKind kind) const;
};
}  // namespace std
#endif

#endif

#ifdef CVC5_API_USE_C_ENUMS
#ifndef CVC5__API__CVC5_C_KIND_H
#define CVC5__API__CVC5_C_KIND_H
#endif
#else
#ifndef CVC5__API__CVC5_CPP_KIND_H
#define CVC5__API__CVC5_CPP_KIND_H
#endif
#endif
