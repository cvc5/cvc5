/*********************                                                        */
/*! \file project_op.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **/

#include "project_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const ProjectOp& op)
{
  out << "(project_op";
  for (const uint32_t& index : op.getIndices())
  {
    out << " " << index;
  }
  out << ')';
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

ProjectOp::ProjectOp(const ProjectOp& op) : d_indices(std::move(op.d_indices))
{
  // ToDo: test this
}

const std::vector<uint32_t>& ProjectOp::getIndices() const { return d_indices; }

bool ProjectOp::operator==(const ProjectOp& op) const
{
  return d_indices == op.d_indices;
}

}  // namespace CVC4
