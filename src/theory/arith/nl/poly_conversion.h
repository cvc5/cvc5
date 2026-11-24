/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for converting to and from LibPoly objects.
 */

#ifndef CVC5__THEORY__ARITH__NL__POLY_CONVERSION_H
#define CVC5__THEORY__ARITH__NL__POLY_CONVERSION_H

#include "cvc5_private.h"

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <cstddef>
#include <map>
#include <utility>
#include <vector>

#include "expr/node.h"
#include "util/real_algebraic_number.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class BoundInference;

namespace nl {

/** Bijective mapping between cvc5 variables and poly variables. */
struct VariableMapper
{
  VariableMapper(const poly::Context& ctx) : polyCtx(ctx) {}
  /** The libpoly context */
  const poly::Context& polyCtx;
  /** A mapping from cvc5 variables to poly variables. */
  std::map<cvc5::internal::Node, poly::Variable> mVarCVCpoly;
  /** A mapping from poly variables to cvc5 variables. */
  std::map<poly::Variable, cvc5::internal::Node> mVarpolyCVC;

  /** Retrieves the according poly variable. */
  poly::Variable operator()(const cvc5::internal::Node& n);
  /** Retrieves the according cvc5 variable. */
  cvc5::internal::Node operator()(const poly::Variable& n);
};

/** Convert a poly univariate polynomial to a cvc5::internal::Node. */
cvc5::internal::Node as_cvc_upolynomial(const poly::UPolynomial& p,
                                        const cvc5::internal::Node& var);

/**
 * Takes a list of polynomials (representing a remainder sequence) and returns
 * another list, which is a pair of elements (a, b) where a is the quocient and
 * b is the remainder. The i-th pair has the element seq[i] of the sequence and
 * the pseudo-quotient of seq[i - 2] by seq[i - 1], of which seq[i] is the
 * remainder up to a constant factor (zero for the first two elements).
 */
std::vector<std::pair<poly::UPolynomial, poly::UPolynomial>> enhancedRemSeq(
    const std::vector<poly::UPolynomial>& seq);

/**
 * Convert a remainder sequence to a cvc5::internal::Node: an SEXPR with the
 * pairs of enhancedRemSeq(seq), each an SEXPR (a b) of polynomials over var.
 */
cvc5::internal::Node as_cvc_remainder_sequence(
    const std::vector<poly::UPolynomial>& seq, const cvc5::internal::Node& var);

/**
 * Convert a cvc5::internal::Node to a poly univariate polynomial. Is robust to
 * n being a `Kind::TO_REAL` wrapper node.
 */
poly::UPolynomial as_poly_upolynomial(const cvc5::internal::Node& n,
                                      const cvc5::internal::Node& var);

/**
 * Constructs a polynomial from the given node.
 *
 * While a Node may contain rationals, a Polynomial does not.
 * We therefore also store the denominator of the returned polynomial and
 * use it to construct the integer polynomial recursively.
 * Once the polynomial has been fully constructed, we can oftentimes ignore the
 * denominator (except for its sign, which is always positive, though).
 * This is the case if we are solely interested in the roots of the polynomials
 * (like in the context of coverings). If we need the actual polynomial (for
 * example in the context of ICP) the second overload provides the denominator
 * in the third argument. The method is robust to n being a `Kind::TO_REAL`
 * wrapper node.
 */
poly::Polynomial as_poly_polynomial(const cvc5::internal::Node& n,
                                    VariableMapper& vm);
poly::Polynomial as_poly_polynomial(const cvc5::internal::Node& n,
                                    VariableMapper& vm,
                                    poly::Rational& denominator);

/**
 * Constructs a node from the given polynomial.
 *
 * This methods does the straight-forward conversion from a polynomial into Node
 * representation, using the given variable mapper.
 * The resulting node is not minimized in any form (it may contain spurious
 * multiplications with one or use NONLINEAR_MULT where regular MULT may be
 * sufficient), so it may be sensible to rewrite it afterwards.
 */
cvc5::internal::Node as_cvc_polynomial(NodeManager* nm,
                                       const poly::Polynomial& p,
                                       VariableMapper& vm);

/**
 * Like as_cvc_polynomial, but a power x^d is expanded into d factors x
 * (nested NONLINEAR_MULT) instead of a POW node. This is the shape expected
 * by the polynomial normalization of ARITH_POLY_NORM (PolyNorm does not
 * handle POW) and by its reconstruction in lean-smt. Used for the terms of
 * the univariate coverings proofs.
 */
cvc5::internal::Node as_cvc_polynomial_no_pow(NodeManager* nm,
                                              const poly::Polynomial& p,
                                              VariableMapper& vm);

/**
 * Like value_to_node, but never returns an integer constant: a real algebraic
 * number that turns out to be rational (e.g. because its isolating interval
 * collapsed to a point) is converted by mkRealAlgebraicNumber through
 * mkConstRealOrInt, which yields an integer constant for integral values.
 * The univariate coverings proofs quantify over a real variable, so their
 * endpoints must be real constants. Used for the terms of these proofs.
 * Irrational real algebraic numbers are returned as
 * REAL_ALGEBRAIC_NUMBER_WITNESS terms (see PolyConverter::ran_to_sturm_witness)
 * whose Sturm sequence is over ran_variable.
 */
Node value_to_node_no_integer(const poly::Value& v, const Node& ran_variable);

/**
 * Constructs a constraints (a polynomial and a sign condition) from the given
 * node.
 */
std::pair<poly::Polynomial, poly::SignCondition> as_poly_constraint(
    Node n, VariableMapper& vm);

Node ran_to_node(const poly::AlgebraicNumber& an, const Node& ran_variable);

/**
 * Transforms a poly::Value to a node.
 * The resulting node can be either a constant, a witness term or plus or minus
 * infinity.
 */
Node value_to_node(const poly::Value& v, const Node& ran_variable);

/**
 * Constructs a lemma that excludes a given interval from the feasible values of
 * a variable. Conceptually, the resulting lemma has the form
 * (OR
 *    (<= var interval.lower)
 *    (<= interval.upper var)
 * )
 * This method honors the interval bound types (open or closed), but also deals
 * with real algebraic endpoints. If allowNonlinearLemma is false, real
 * algebraic endpoints are reflected by coarse (numeric) approximations and thus
 * may lead to lemmas that are weaker than they could be. Also, lemma creation
 * may fail altogether.
 * If allowNonlinearLemma is true, it tries to construct better lemmas (based on
 * the sign of the defining polynomial of the real algebraic number). These
 * lemmas are nonlinear, though, and may thus be expensive to use in the
 * subsequent solving process.
 */
Node excluding_interval_to_lemma(const Node& variable,
                                 const poly::Interval& interval,
                                 bool allowNonlinearLemma);

/**
 * Transforms a node to a poly::AlgebraicNumber.
 * Expects a node of the following form:
 * (AND
 *    (= (polynomial in __z) 0)
 *    (< CONST __z)
 *    (< __z CONST)
 * )
 */
poly::AlgebraicNumber node_to_poly_ran(const Node& n, const Node& ran_variable);

/**
 * Transforms a node to a poly::Value.
 */
poly::Value node_to_value(const Node& n, const Node& ran_variable);

/**
 * Give a rough estimate of the bitsize of the representation of `v`.
 * It can be used as a rough measure of the size of complexity of a value, for
 * example to avoid divergence or disallow huge lemmas.
 */
std::size_t bitsize(const poly::Value& v);

poly::IntervalAssignment getBounds(VariableMapper& vm,
                                   const BoundInference& bi);

}  // namespace nl
}  // namespace arith
}  // namespace theory

class PolyConverter
{
 public:
  /**
   * Transforms a real algebraic number to a node suitable for putting it into a
   * model. The resulting node can be either a constant (suitable for
   * addSubstitution) or a witness term (suitable for addWitness).
   */
  static Node ran_to_node(const RealAlgebraicNumber& ran,
                          const Node& ran_variable);
  /**
   * Get the defining polynomial for the given ran, expressed over variable
   * ran_variable. Returns null if the defining polynomial does not exist.
   */
  static Node ran_to_defining_polynomial(const RealAlgebraicNumber& ran,
                                         const Node& ran_variable);
  /**
   * Get a REAL_ALGEBRAIC_NUMBER_WITNESS node for the given ran: the ran
   * together with the Sturm sequence of its defining polynomial (an SEXPR of
   * polynomials over variable ran_variable). Returns null if the ran is
   * represented by a rational (and hence has no defining polynomial).
   */
  static Node ran_to_sturm_witness(const RealAlgebraicNumber& ran,
                                   const Node& ran_variable);
  /**
   * Get the lower bound for the given ran, which is a constant real.
   */
  static Node ran_to_lower(NodeManager* nm, const RealAlgebraicNumber& ran);
  /**
   * Get the upper bound for the given ran, which is a constant real.
   */
  static Node ran_to_upper(NodeManager* nm, const RealAlgebraicNumber& ran);

  /**
   * Gets the list of coefficients of `ran` as a `Node`.
   */
  static Node ran_to_coeffs(NodeManager* nm, const RealAlgebraicNumber& ran);

  /** Transforms a node to a RealAlgebraicNumber by calling node_to_poly_ran. */
  static RealAlgebraicNumber node_to_ran(const Node& n,
                                         const Node& ran_variable);
};

}  // namespace cvc5::internal

#endif

#endif
