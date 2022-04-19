/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for TableProjectOp operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__TABLE_PROJECT_OP_H
#define CVC5__TABLE_PROJECT_OP_H

#include "theory/datatypes/tuple_project_op.h"

namespace cvc5::internal {

/**
 * The class is an operator for kind project used to project elements in a
 * table. It stores the indices of projected elements
 */
class TableProjectOp : public TupleProjectOp
{
 public:
  explicit TableProjectOp(std::vector<uint32_t> indices);
  TableProjectOp(const TableProjectOp& op) = default;
}; /* class TableProjectOp */

/**
 * Hash function for the TupleProjectOpHashFunction objects.
 */
struct TableProjectOpHashFunction : public TupleProjectOpHashFunction
{
}; /* struct TupleProjectOpHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__TABLE_PROJECT_OP_H */
