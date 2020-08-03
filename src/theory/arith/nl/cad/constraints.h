/*********************                                                        */
/*! \file constraints.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements a container for CAD constraints.
 **
 ** Implements a container for CAD constraints.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__NL__CAD__CONSTRAINTS_H
#define CVC4__THEORY__ARITH__NL__CAD__CONSTRAINTS_H

#include "util/real_algebraic_number.h"

#ifdef CVC4_POLY_IMP

#include <poly/polyxx.h>

#include <map>
#include <tuple>
#include <vector>

#include "expr/kind.h"
#include "expr/node_manager_attributes.h"
#include "theory/arith/nl/poly_conversion.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

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
   * A mapping from CVC4 variables to poly variables.
   */
  VariableMapper d_varMapper;

  void sortConstraints();
};

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif

#endif
