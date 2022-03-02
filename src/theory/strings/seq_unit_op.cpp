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
 * A class for sequence unit
 */

#include "theory/strings/seq_unit_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const SeqUnitOp& op)
{
  return out << "(SeqUnitOp " << op.getType() << ')';
}

size_t SeqUnitOpHashFunction::operator()(const SeqUnitOp& op) const
{
  return std::hash<TypeNode>()(op.getType());
}

SeqUnitOp::SeqUnitOp(const TypeNode& elementType)
    : d_type(new TypeNode(elementType))
{
}

SeqUnitOp::SeqUnitOp(const SeqUnitOp& op) : d_type(new TypeNode(op.getType()))
{
}

const TypeNode& SeqUnitOp::getType() const { return *d_type; }

bool SeqUnitOp::operator==(const SeqUnitOp& op) const
{
  return getType() == op.getType();
}

}  // namespace cvc5
