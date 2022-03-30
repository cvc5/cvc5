/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic theory state.
 */

#include "theory/arith/arith_state.h"

#include "theory/arith/theory_arith_private.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

ArithState::ArithState(Env& env, Valuation val)
    : TheoryState(env, val), d_parent(nullptr)
{
}

bool ArithState::isInConflict() const
{
  return d_parent->anyConflict() || d_conflict;
}

void ArithState::setParent(TheoryArithPrivate* p) { d_parent = p; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
