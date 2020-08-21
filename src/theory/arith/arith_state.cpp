/*********************                                                        */
/*! \file arith_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic theory state.
 **/

#include "theory/arith/arith_state.h"

#include "theory/arith/theory_arith_private.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithState::ArithState(TheoryArithPrivate& parent,
                       context::Context* c,
                       context::UserContext* u,
                       Valuation val)
    : TheoryState(c, u, val), d_parent(parent)
{
}

bool ArithState::isInConflict() const
{
  return d_parent.anyConflict() || d_conflict;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
