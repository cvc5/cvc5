/*********************                                                        */
/*! \file eager_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The eager solver
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__EAGER_SOLVER_H
#define CVC4__THEORY__STRINGS__EAGER_SOLVER_H

#include <map>

#include "expr/node.h"
#include "theory/strings/eqc_info.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Eager solver
 */
class EagerSolver
{
 public:
  EagerSolver(SolverState& state);
  ~EagerSolver();
  /** called when a new equivalence class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalence classes merge */
  void eqNotifyMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
private:
  /** Reference to the solver state */
  SolverState& d_state;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__EAGER_SOLVER_H */
