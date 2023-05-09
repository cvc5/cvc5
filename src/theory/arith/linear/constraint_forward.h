/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Forward declarations of the ConstraintValue and ConstraintDatabase
 * classes.
 *
 * This is the forward declarations of the ConstraintValue and
 * ConstraintDatabase and the typedef for Constraint.
 * This is used to break circular dependencies and minimize interaction
 * between header files.
 */

#ifndef CVC5__THEORY__ARITH__CONSTRAINT_FORWARD_H
#define CVC5__THEORY__ARITH__CONSTRAINT_FORWARD_H

#include <vector>

#include "cvc5_private.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class Constraint;
typedef Constraint* ConstraintP;
typedef const Constraint* ConstraintCP;

static constexpr ConstraintP NullConstraint = nullptr;

class ConstraintDatabase;

typedef std::vector<ConstraintCP> ConstraintCPVec;

typedef std::vector<Rational> RationalVector;
typedef RationalVector* RationalVectorP;
typedef const RationalVector* RationalVectorCP;
static constexpr RationalVectorCP RationalVectorCPSentinel = nullptr;
static constexpr RationalVectorP RationalVectorPSentinel = nullptr;

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__CONSTRAINT_FORWARD_H */
