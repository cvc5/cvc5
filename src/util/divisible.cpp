/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Divisibility-by-k predicate.
 */

#include "util/divisible.h"

#include "base/check.h"
#include "base/exception.h"

using namespace std;

namespace cvc5::internal {

Divisible::Divisible(const Integer& n) : k(n) {
  Assert(n > 0) << "Divisible predicate must be constructed over positive N";
}

}  // namespace cvc5::internal
