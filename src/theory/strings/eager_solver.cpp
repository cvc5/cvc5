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

#include "theory/strings/eager_solver.h"

namespace CVC4 {
namespace theory {
namespace strings {


EagerSolver::EagerSolver(SolverState& state) : d_state(state) {}

EagerSolver::~EagerSolver() {}

void EagerSolver::eqNotifyNewClass(TNode t)
{
  
}

void EagerSolver::eqNotifyMerge(TNode t1, TNode t2)
{
}

void EagerSolver::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
}


}  // namespace strings
}  // namespace theory
}  // namespace CVC4
