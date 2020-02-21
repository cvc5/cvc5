/*********************                                                        */
/*! \file sat_solver_types.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementations of SAT solver type operations which require large
 ** std headers.
 **
 **/

#include "prop/sat_solver_types.h"

#include <algorithm>

namespace CVC4 {
namespace prop {
bool SatClauseLessThan::operator()(const SatClause& l, const SatClause& r) const
{
  return std::lexicographical_compare(l.begin(), l.end(), r.begin(), r.end());
}
}  // namespace prop
}  // namespace CVC4
