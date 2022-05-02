/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for TupleProjectOp operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__PROJECT_OP_H
#define CVC5__PROJECT_OP_H

#include <ostream>
#include <vector>

namespace cvc5::internal {

class TypeNode;

/**
 * base class for TupleProjectOp, TupleProjectOp
 */
class ProjectOp
{
 public:
  explicit ProjectOp(std::vector<uint32_t> indices);
  ProjectOp(const ProjectOp& op) = default;

  /** return the indices of the projection */
  const std::vector<uint32_t>& getIndices() const;

  bool operator==(const ProjectOp& op) const;

 private:
  std::vector<uint32_t> d_indices;
}; /* class ProjectOp */

std::ostream& operator<<(std::ostream& out, const ProjectOp& op);

/**
 * Hash function for the ProjectOpHashFunction objects.
 */
struct ProjectOpHashFunction
{
  size_t operator()(const ProjectOp& op) const;
}; /* struct ProjectOpHashFunction */

/**
 * The class is an operator for kind project used to project elements in a
 * table. It stores the indices of projected elements
 */
class TupleProjectOp : public ProjectOp
{
 public:
  explicit TupleProjectOp(std::vector<uint32_t> indices);
  TupleProjectOp(const TupleProjectOp& op) = default;
}; /* class TupleProjectOp */

/**
 * Hash function for the TupleProjectOpHashFunction objects.
 */
struct TupleProjectOpHashFunction : public ProjectOpHashFunction
{
}; /* struct TupleProjectOpHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__PROJECT_OP_H */
