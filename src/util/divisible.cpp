/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King
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

#include "util/divisible.h"

#include "base/check.h"
#include "base/exception.h"

using namespace std;

namespace cvc5 {

Divisible::Divisible(const Integer& n) : k(n) {
  PrettyCheckArgument(n > 0, n, "Divisible predicate must be constructed over positive N");
}

}  // namespace cvc5
