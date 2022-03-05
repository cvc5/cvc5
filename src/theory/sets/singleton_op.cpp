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
 * A class for singleton operator for sets.
 */

#include "theory/sets/singleton_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const SetSingletonOp& op)
{
  return out << "(SetSingletonOp " << op.getType() << ')';
}

size_t SetSingletonOpHashFunction::operator()(const SetSingletonOp& op) const
{
  return std::hash<TypeNode>()(op.getType());
}

SetSingletonOp::SetSingletonOp(const TypeNode& elementType)
    : d_type(new TypeNode(elementType))
{
}

SetSingletonOp::SetSingletonOp(const SetSingletonOp& op)
    : d_type(new TypeNode(op.getType()))
{
}

const TypeNode& SetSingletonOp::getType() const { return *d_type; }

bool SetSingletonOp::operator==(const SetSingletonOp& op) const
{
  return getType() == op.getType();
}

}  // namespace cvc5
