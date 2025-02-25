/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Defines pseudo-Boolean types and utilities, including:
 * - Enumerations for pseudo-Boolean values and solver states.
 * - Classes for pseudo-Boolean variables and literals.
 * - Classes for pseudo-Boolean constraints and constraint sets, with
 *   constraints stored as Nodes to leverage hash consing.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__PB__PB_TYPES_H
#define CVC5__THEORY__BV__PB__PB_TYPES_H

#include "util/integer.h"
#include "expr/node.h"

#include <string>

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

/**
 * Represents the possible values of a Pseudo-Boolean variable.
 * These values are used to describe the assignment or state of a variable.
 */
enum class PbValue { UNKNOWN, TRUE, FALSE };

/**
 * Represents the possible states of a Pseudo-Boolean solver.
 * These states indicate the outcome or current status of the solver.
 */
enum class PbSolveState { UNKNOWN, SAT, UNSAT };

/**
 * A pseudo-Boolean variable identified by a unique ID.
 */
class PbVariable
{
 public:
  explicit PbVariable(const Integer& id);
  explicit PbVariable(const int& id);

  friend std::ostream& operator<<(std::ostream& os, const PbVariable& var);

 private:
  std::string id;
};

/**
 * A pseudo-Boolean literal, consisting of a variable and its polarity.
 */
class PbLiteral
{
 public:
  explicit PbLiteral(const PbVariable& var, const bool p = true);
  explicit PbLiteral(const Integer& id, const bool p = true);
  explicit PbLiteral(const int& id, const bool p = true);

  friend std::ostream& operator<<(std::ostream& os, const PbLiteral& var);

  Node toNode(NodeManager* nm) const;

 private:
  PbVariable variable;
  bool polarity;
};

/**
 * Represents a pseudo-Boolean constraint, which is a linear inequality or
 * equality involving pseudo-Boolean literals and coefficients.
 * The constraint is stored in a Node to leverage hash consing.
 */
class PbConstraint
{
 public:
  explicit PbConstraint(const std::vector<PbLiteral>& literals,
                        const std::vector<Integer>& coefficients,
                        Kind relationalOperator,
                        const Integer& constant,
                        NodeManager* nm);
  explicit PbConstraint(const PbLiteral& literal,
                        const Integer& coefficient,
                        Kind relationalOperator,
                        const Integer& constant,
                        NodeManager* nm);
  Node toNode() const;

 private:
  Node constraint;
  std::vector<Node> generateProducts(const std::vector<PbLiteral>& literals,
                                     const std::vector<Integer>& coefficients,
                                     NodeManager* nm);
};


/**
 * Represents a set of pseudo-Boolean constraints.
 * The set of constraints is stored in a Node to leverage hash consing.
 */
class PbConstraintSet
{
 public:
  explicit PbConstraintSet(const std::set<PbConstraint> constraints,
                           NodeManager* nm);

 private:
  Node constraintSet;
};

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__BV__PB__PB_TYPES_H
