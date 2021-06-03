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
 * A class for TupleProjectOp operator.
 */

#include "tuple_project_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const TupleProjectOp& op)
{
  for (const uint32_t& index : op.getIndices())
  {
    out << " " << index;
  }
  return out;
}

size_t TupleProjectOpHashFunction::operator()(const TupleProjectOp& op) const
{
  // we expect most tuples to have length < 10.
  // Therefore we can implement a simple hash function
  size_t hash = 0;
  for (uint32_t index : op.getIndices())
  {
    hash = hash * 10 + index;
  }
  return hash;
}

TupleProjectOp::TupleProjectOp(std::vector<uint32_t> indices)
    : d_indices(std::move(indices))
{
}

const std::vector<uint32_t>& TupleProjectOp::getIndices() const { return d_indices; }

bool TupleProjectOp::operator==(const TupleProjectOp& op) const
{
  return d_indices == op.d_indices;
}

}  // namespace cvc5
