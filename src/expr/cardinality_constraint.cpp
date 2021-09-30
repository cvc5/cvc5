/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const CardinalityConstraint& cc)
{
  return out << "fmf.card(" << cc.getType() << ", " << cc.getUpperBound()
             << ')';
}

/**
 * Constructs an emptyset of the specified type. Note that the argument
 * is the type of the set itself, NOT the type of the elements.
 */
CardinalityConstraint::CardinalityConstraint(const TypeNode& setType,
                                             const Integer& ub)
    : d_type(new TypeNode(setType)), d_ubound(ub)
{
}

CardinalityConstraint::CardinalityConstraint(const CardinalityConstraint& cc)
    : d_type(new TypeNode(cc.getType())), d_ubound(cc.getUpperBound())
{
}

CardinalityConstraint& CardinalityConstraint::operator=(
    const CardinalityConstraint& cc)
{
  (*d_type) = cc.getType();
  d_ubound = cc.getUpperBound();
  return *this;
}

CardinalityConstraint::~CardinalityConstraint() {}

const TypeNode& CardinalityConstraint::getType() const { return *d_type; }

const TypeNode& CardinalityConstraint::getType() const { return *d_type; }

bool CardinalityConstraint::operator==(const CardinalityConstraint& cc) const
{
  return getType() == cc.getType() && getUpperBound() == cc.getUpperBound();
}

bool CardinalityConstraint::operator!=(const CardinalityConstraint& cc) const
{
  return !(*this == cc);
}
bool CardinalityConstraint::operator<(const CardinalityConstraint& cc) const
{
  return getType() < cc.getType();
}

bool CardinalityConstraint::operator<=(const CardinalityConstraint& cc) const
{
  return getType() <= cc.getType();
}

bool CardinalityConstraint::operator>(const CardinalityConstraint& cc) const
{
  return !(*this <= cc);
}

bool CardinalityConstraint::operator>=(const CardinalityConstraint& cc) const
{
  return !(*this < cc);
}

}  // namespace cvc5
