/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for BAG_MAKE operator.
 */

#include "bag_make_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const BagMakeOp& op)
{
  return out << "(BagMakeOp " << op.getType() << ')';
}

size_t BagMakeOpHashFunction::operator()(const BagMakeOp& op) const
{
  return std::hash<TypeNode>()(op.getType());
}

BagMakeOp::BagMakeOp(const TypeNode& elementType)
    : d_type(new TypeNode(elementType))
{
}

BagMakeOp::BagMakeOp(const BagMakeOp& op) : d_type(new TypeNode(op.getType()))
{
}

const TypeNode& BagMakeOp::getType() const { return *d_type; }

bool BagMakeOp::operator==(const BagMakeOp& op) const
{
  return getType() == op.getType();
}

}  // namespace cvc5
