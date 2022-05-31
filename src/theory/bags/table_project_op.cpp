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

#include "table_project_op.h"

namespace cvc5::internal {

TableProjectOp::TableProjectOp(std::vector<uint32_t> indices)
    : ProjectOp(std::move(indices))
{
}

TableAggregateOp::TableAggregateOp(std::vector<uint32_t> indices)
    : ProjectOp(std::move(indices))
{
}

TableJoinOp::TableJoinOp(std::vector<uint32_t> indices)
    : ProjectOp(std::move(indices))
{
}

TableGroupOp::TableGroupOp(std::vector<uint32_t> indices)
    : ProjectOp(std::move(indices))
{
}

}  // namespace cvc5::internal
