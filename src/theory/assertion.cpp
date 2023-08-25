/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory assertions.
 */

#include "theory/assertion.h"

namespace cvc5::internal {
namespace theory {

std::ostream& operator<<(std::ostream& out, const Assertion& a) {
  return out << a.d_assertion;
}

}  // namespace theory
}  // namespace cvc5::internal
