/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner
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

#include "cvc5_public.h"

#ifndef CVC5__PROJECT_OP_H
#define CVC5__PROJECT_OP_H

#include <ostream>
#include <vector>

namespace cvc5 {

class TypeNode;

/**
 * The class is an operator for kind project used to project elements in a tuple
 * It stores the indices of projected elements
 */
class TupleProjectOp
{
 public:
  explicit TupleProjectOp(std::vector<uint32_t> indices);
  TupleProjectOp(const TupleProjectOp& op) = default;

  /** return the indices of the projection */
  const std::vector<uint32_t>& getIndices() const;

  bool operator==(const TupleProjectOp& op) const;

 private:
  std::vector<uint32_t> d_indices;
}; /* class TupleProjectOp */

std::ostream& operator<<(std::ostream& out, const TupleProjectOp& op);

/**
 * Hash function for the TupleProjectOpHashFunction objects.
 */
struct TupleProjectOpHashFunction
{
  size_t operator()(const TupleProjectOp& op) const;
}; /* struct TupleProjectOpHashFunction */

}  // namespace cvc5

#endif /* CVC5__PROJECT_OP_H */
