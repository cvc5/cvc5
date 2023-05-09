/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic evaluator.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_EVALUATOR_H
#define CVC5__THEORY__ARITH__ARITH_EVALUATOR_H

#include <optional>

#include "expr/node.h"
#include "smt/env.h"
#include "theory/arith/arith_subs.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * Check if the expression `expr` is zero over the given model.
 * The model subs may contain real algebraic numbers in standard
 * witness form. The environment is used for rewriting.
 *
 * The result is true or false, if the expression could be evaluated. If it
 * could not, possibly in the presence of a transcendental model, the result is
 * std::nullopt.
 */
std::optional<bool> isExpressionZero(Env& env,
                                     Node expr,
                                     const ArithSubs& subs);
}
}  // namespace theory
}  // namespace cvc5::internal

#endif
