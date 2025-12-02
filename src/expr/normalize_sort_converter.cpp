/******************************************************************************
 * Top contributors (to current version):
 *   Daneshvar Amrollahi
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 *
 */

#include "expr/normalize_sort_converter.h"

#include <unordered_map>

namespace cvc5::internal {

NormalizeSortNodeConverter::NormalizeSortNodeConverter(
    const std::unordered_map<TypeNode, TypeNode>& normalizedSorts,
    NodeManager* nm)
    : NodeConverter(nm), d_normalizedSorts(normalizedSorts)
{
}

TypeNode NormalizeSortNodeConverter::postConvertType(TypeNode tn)
{
  auto it = d_normalizedSorts.find(tn);
  if (it != d_normalizedSorts.end())
  {
    return it->second;
  }
  return tn;
}

}  // namespace cvc5::internal
