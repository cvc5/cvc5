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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__ARITH_STATE_H
#define CVC4__THEORY__ARITH__ARITH_STATE_H

#include "theory/theory_state.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArithPrivate;

/**
 * The arithmetic state.
 *
 * This is a wrapper for making a state object out of TheoryArithPrivate.
 */
class ArithState : public TheoryState
{
 public:
  ArithState(TheoryArithPrivate& parent,
             context::Context* c,
             context::UserContext* u,
             Valuation val);
  ~ArithState() {}
  /** Are we currently in conflict? */
  bool isInConflict() const override;

 private:
  /** reference to parent */
  TheoryArithPrivate& d_parent;
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
