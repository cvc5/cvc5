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

CardinalityConstraint::CardinalityConstraint(const TypeNode& setType,
                                             const Integer& ub)
    : d_type(new TypeNode(setType)), d_ubound(ub)
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

CombinedCardinalityConstraint::CombinedCardinalityConstraint(const Integer& ub)
    : d_ubound(ub)
{
}

CombinedCardinalityConstraint::~CombinedCardinalityConstraint() {}

const Integer& CombinedCardinalityConstraint::getUpperBound() const { return d_ubound; }

bool CombinedCardinalityConstraint::operator==(const CombinedCardinalityConstraint& cc) const
{
  return getUpperBound() == cc.getUpperBound();
}

bool CombinedCardinalityConstraint::operator!=(const CombinedCardinalityConstraint& cc) const
{
  return !(*this == cc);
}

std::ostream& operator<<(std::ostream& out, const CombinedCardinalityConstraint& cc)
{
  return out << "fmf.card(" << cc.getUpperBound() << ')';
}

}  // namespace cvc5
