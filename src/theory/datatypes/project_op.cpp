/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for ProjectOp operator.
 */

#include "project_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const ProjectOp& op)
{
  // should only be used for debugging, not in the smt2 printer.
  const std::vector<uint32_t>& indices = op.getIndices();
  if (indices.empty())
  {
    out << "ProjectOp";
  }
  else
  {
    out << "(ProjectOp ";
    for (const uint32_t& index : op.getIndices())
    {
      out << " " << index;
    }
    out << ")";
  }
  return out;
}

size_t ProjectOpHashFunction::operator()(const ProjectOp& op) const
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

ProjectOp::ProjectOp(std::vector<uint32_t> indices)
    : d_indices(std::move(indices))
{
}

const std::vector<uint32_t>& ProjectOp::getIndices() const { return d_indices; }

bool ProjectOp::operator==(const ProjectOp& op) const
{
  return d_indices == op.d_indices;
}

}  // namespace cvc5::internal
