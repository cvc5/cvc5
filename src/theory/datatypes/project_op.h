/*********************                                                        */
/*! \file project_op.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief a class for ProjectOp operator
 **/

#include "cvc4_public.h"

#ifndef CVC4__PROJECT_OP_H
#define CVC4__PROJECT_OP_H

#include <ostream>
#include <vector>

namespace CVC4 {

class TypeNode;

/**
 * The class is an operator for kind project used to project elements in a tuple
 * It stores the indices of projected elements
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
struct CVC4_PUBLIC ProjectOpHashFunction
{
  size_t operator()(const ProjectOp& op) const;
}; /* struct ProjectOpHashFunction */

}  // namespace CVC4

#endif /* CVC4__PROJECT_OP_H */
