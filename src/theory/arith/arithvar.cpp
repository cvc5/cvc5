/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/arith/arithvar.h"
#include <limits>
#include <set>

namespace cvc5 {
namespace theory {
namespace arith {

const ArithVar ARITHVAR_SENTINEL = std::numeric_limits<ArithVar>::max();

bool debugIsASet(const std::vector<ArithVar>& variables){
  std::set<ArithVar> asSet(variables.begin(), variables.end());
  return asSet.size() == variables.size();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
