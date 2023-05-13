/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementations of SAT solver type operations which require large std
 * headers.
 */

#include "prop/sat_solver_types.h"

#include <algorithm>

namespace cvc5::internal {
namespace prop {
bool SatClauseLessThan::operator()(const SatClause& l, const SatClause& r) const
{
  return std::lexicographical_compare(l.begin(), l.end(), r.begin(), r.end());
}
}  // namespace prop
}  // namespace cvc5::internal
