/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cardinality constraint operator
 */

#include "expr/cardinality_constraint.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

CardinalityConstraint::CardinalityConstraint(const TypeNode& type,
                                             const Integer& ub)
    : d_type(new TypeNode(type)), d_ubound(ub)
{
  AlwaysAssert(type.isUninterpretedSort())
      << "Unexpected cardinality constraints for " << type;
}

CardinalityConstraint::CardinalityConstraint(const CardinalityConstraint& other)
    : d_type(new TypeNode(other.getType())), d_ubound(other.getUpperBound())
{
}

CardinalityConstraint::~CardinalityConstraint() {}

const TypeNode& CardinalityConstraint::getType() const { return *d_type; }

const Integer& CardinalityConstraint::getUpperBound() const { return d_ubound; }

bool CardinalityConstraint::operator==(const CardinalityConstraint& cc) const
{
  return getType() == cc.getType() && getUpperBound() == cc.getUpperBound();
}

bool CardinalityConstraint::operator!=(const CardinalityConstraint& cc) const
{
  return !(*this == cc);
}

std::ostream& operator<<(std::ostream& out, const CardinalityConstraint& cc)
{
  return out << "fmf.card(" << cc.getType() << ", " << cc.getUpperBound()
             << ')';
}

size_t CardinalityConstraintHashFunction::operator()(
    const CardinalityConstraint& cc) const
{
  return std::hash<TypeNode>()(cc.getType())
         * IntegerHashFunction()(cc.getUpperBound());
}

CombinedCardinalityConstraint::CombinedCardinalityConstraint(const Integer& ub)
    : d_ubound(ub)
{
}

CombinedCardinalityConstraint::CombinedCardinalityConstraint(
    const CombinedCardinalityConstraint& other)
    : d_ubound(other.getUpperBound())
{
}

CombinedCardinalityConstraint::~CombinedCardinalityConstraint() {}

const Integer& CombinedCardinalityConstraint::getUpperBound() const
{
  return d_ubound;
}

bool CombinedCardinalityConstraint::operator==(
    const CombinedCardinalityConstraint& cc) const
{
  return getUpperBound() == cc.getUpperBound();
}

bool CombinedCardinalityConstraint::operator!=(
    const CombinedCardinalityConstraint& cc) const
{
  return !(*this == cc);
}

std::ostream& operator<<(std::ostream& out,
                         const CombinedCardinalityConstraint& cc)
{
  return out << "fmf.card(" << cc.getUpperBound() << ')';
}

size_t CombinedCardinalityConstraintHashFunction::operator()(
    const CombinedCardinalityConstraint& cc) const
{
  return cc.getUpperBound().hash();
}

}  // namespace cvc5::internal
