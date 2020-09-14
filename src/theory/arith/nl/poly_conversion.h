/*********************                                                        */
/*! \file poly_conversion.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for converting to and from LibPoly objects.
 **
 ** Utilities for converting to and from LibPoly objects.
 **/

#ifndef CVC4__THEORY__ARITH__NL__POLY_CONVERSION_H
#define CVC4__THEORY__ARITH__NL__POLY_CONVERSION_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP

#include <poly/polyxx.h>

#include <iostream>

#include "expr/node.h"
#include "util/real_algebraic_number.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

/** Bijective mapping between CVC4 variables and poly variables. */
struct VariableMapper
{
  /** A mapping from CVC4 variables to poly variables. */
  std::map<CVC4::Node, poly::Variable> mVarCVCpoly;
  /** A mapping from poly variables to CVC4 variables. */
  std::map<poly::Variable, CVC4::Node> mVarpolyCVC;

  /** Retrieves the according poly variable. */
  poly::Variable operator()(const CVC4::Node& n);
  /** Retrieves the according CVC4 variable. */
  CVC4::Node operator()(const poly::Variable& n);
};

/** Convert a poly univariate polynomial to a CVC4::Node. */
CVC4::Node as_cvc_upolynomial(const poly::UPolynomial& p,
                              const CVC4::Node& var);

/** Convert a CVC4::Node to a poly univariate polynomial. */
poly::UPolynomial as_poly_upolynomial(const CVC4::Node& n,
                                      const CVC4::Node& var);

/**
 * Constructs a polynomial from the given node.
 *
 * While a Node may contain rationals, a Polynomial does not.
 * We therefore also store the denominator of the returned polynomial and
 * use it to construct the integer polynomial recursively.
 * Once the polynomial has been fully constructed, we can ignore the
 * denominator (except for its sign, which is always positive, though).
 */
poly::Polynomial as_poly_polynomial(const CVC4::Node& n, VariableMapper& vm);

/**
 * Constructs a constraints (a polynomial and a sign condition) from the given
 * node.
 */
std::pair<poly::Polynomial, poly::SignCondition> as_poly_constraint(
    Node n, VariableMapper& vm);

/**
 * Transforms a real algebraic number to a node suitable for putting it into a
 * model. The resulting node can be either a constant (suitable for
 * addCheckModelSubstitution) or a witness term (suitable for
 * addCheckModelWitness).
 */
Node ran_to_node(const RealAlgebraicNumber& ran, const Node& ran_variable);

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

/** Transforms a node to a RealAlgebraicNumber by calling node_to_poly_ran. */
RealAlgebraicNumber node_to_ran(const Node& n, const Node& ran_variable);

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

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif

#endif
