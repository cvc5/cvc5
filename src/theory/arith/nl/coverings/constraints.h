/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements a container for coverings constraints.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__CONSTRAINTS_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__CONSTRAINTS_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <tuple>
#include <vector>

#include "theory/arith/nl/poly_conversion.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

class Constraints
{
 public:
  /** Type alias for a list of constraints. */
  using Constraint = std::tuple<poly::Polynomial, poly::SignCondition, Node>;
  using ConstraintVector = std::vector<Constraint>;

  VariableMapper& varMapper() { return d_varMapper; }

  /**
   * Add a constraint (represented by a polynomial and a sign condition) to the
   * list of constraints.
   */
  void addConstraint(const poly::Polynomial& lhs,
                     poly::SignCondition sc,
                     Node n);

  /**
   * Add a constraints (represented by a node) to the list of constraints.
   * The given node can either be a negation (NOT) or a suitable relation symbol
   * as checked by is_suitable_relation().
   */
  void addConstraint(Node n);

  /**
   * Gives the list of added constraints.
   */
  const ConstraintVector& getConstraints() const;

  /**
   * Remove all constraints.
   */
  void reset();

 private:
  /**
   * A list of constraints, each comprised of a polynomial and a sign
   * condition.
   */
  ConstraintVector d_constraints;

  /**
   * A mapping from cvc5 variables to poly variables.
   */
  VariableMapper d_varMapper;

  void sortConstraints();
};

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

#endif
