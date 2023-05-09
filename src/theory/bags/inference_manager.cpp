/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the inference manager for the theory of bags.
 */

#include "theory/bags/inference_manager.h"

#include "theory/bags/solver_state.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

InferenceManager::InferenceManager(Env& env, Theory& t, SolverState& s)
    : InferenceManagerBuffered(env, t, s, "theory::bags::"), d_state(s)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

void InferenceManager::doPending()
{
  doPendingFacts();
  if (d_state.isInConflict())
  {
    // just clear the pending vectors, nothing else to do
    clearPendingLemmas();
    clearPendingPhaseRequirements();
    return;
  }
  doPendingLemmas();
  doPendingPhaseRequirements();
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
