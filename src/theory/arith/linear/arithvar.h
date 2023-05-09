/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Defines ArithVar which is the internal representation of variables in
 * arithmetic
 *
 * This defines ArithVar which is the internal representation of variables in
 * arithmetic. This is a typedef from Index to ArithVar.
 * This file also provides utilities for ArithVars.
 */

#include "cvc5_private.h"

#pragma once

#include <vector>

#include "util/index.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

typedef Index ArithVar;
extern const ArithVar ARITHVAR_SENTINEL;

typedef std::vector<ArithVar> ArithVarVec;
typedef std::pair<ArithVar, Rational> ArithRatPair;
typedef std::vector< ArithRatPair > ArithRatPairVec;

extern bool debugIsASet(const ArithVarVec& variables);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
