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
 * A class for MK_BAG operator.
 */

#include "make_bag_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const MakeBagOp& op)
{
  return out << "(mkBag_op " << op.getType() << ')';
}

size_t MakeBagOpHashFunction::operator()(const MakeBagOp& op) const
{
  return TypeNodeHashFunction()(op.getType());
}

MakeBagOp::MakeBagOp(const TypeNode& elementType)
    : d_type(new TypeNode(elementType))
{
}

MakeBagOp::MakeBagOp(const MakeBagOp& op) : d_type(new TypeNode(op.getType()))
{
}

const TypeNode& MakeBagOp::getType() const { return *d_type; }

bool MakeBagOp::operator==(const MakeBagOp& op) const
{
  return getType() == op.getType();
}

}  // namespace cvc5
