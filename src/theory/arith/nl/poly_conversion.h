/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 * (like in the context of coverings). If we need the actual polynomial (for example
 * in the context of ICP) the second overload provides the denominator in the
 * third argument.
 * The method is robust to n being a `Kind::TO_REAL` wrapper node.
 */
poly::Polynomial as_poly_polynomial(const cvc5::internal::Node& n, VariableMapper& vm);
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
cvc5::internal::Node as_cvc_polynomial(const poly::Polynomial& p, VariableMapper& vm);

/**
 * Constructs a constraints (a polynomial and a sign condition) from the given
 * node.
 */
std::pair<poly::Polynomial, poly::SignCondition> as_poly_constraint(
    Node n, VariableMapper& vm);

Node ran_to_node(const poly::AlgebraicNumber& an, const Node& ran_variable);

/**
 * Transforms a poly::Value to a node.
 * The resulting node can be either a constant or a witness term.
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

poly::IntervalAssignment getBounds(VariableMapper& vm, const BoundInference& bi);

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
   * Get the lower bound for the given ran, which is a constant real.
   */
  static Node ran_to_lower(const RealAlgebraicNumber& ran);
  /**
   * Get the upper bound for the given ran, which is a constant real.
   */
  static Node ran_to_upper(const RealAlgebraicNumber& ran);

  /** Transforms a node to a RealAlgebraicNumber by calling node_to_poly_ran. */
  static RealAlgebraicNumber node_to_ran(const Node& n,
                                         const Node& ran_variable);
};

}  // namespace cvc5::internal

#endif

#endif
