/*********************                                                        */
/*! \file solver_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags state object
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H
#define CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H

#include <map>
#include <vector>

#include "theory/bags/skolem_cache.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace bags {

class TheoryBagsPrivate;

/** Bags state
 *
 * The purpose of this class is to maintain information concerning the current
 * set of assertions during a full effort check.
 *
 * During a full effort check, the solver for theory of bags should call:
 *   reset; ( registerEqc | registerTerm )*
 * to initialize the information in this class regarding full effort checks.
 * Other query calls are then valid for the remainder of the full effort check.
 */
class SolverState : public TheoryState
{
 public:
  SolverState(context::Context* c,
              context::UserContext* u,
              Valuation val,
              SkolemCache& skc);

  //-------------------------------- initialize per check

 private:
  /** constants */
  Node d_true;
  Node d_false;

  /** Reference to skolem cache */
  SkolemCache& d_skCache;
}; /* class SolverState */

}  // namespace bags
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__THEORY_SOLVER_STATE_H */
