/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Shared solver in the distributed architecture.
 */

#include "theory/shared_solver_distributed.h"

#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace theory {

SharedSolverDistributed::SharedSolverDistributed(Env& env, TheoryEngine& te)
    : SharedSolver(env, te)
{
}

bool SharedSolverDistributed::needsEqualityEngine(theory::EeSetupInfo& esi)
{
  return d_sharedTerms.needsEqualityEngine(esi);
}

void SharedSolverDistributed::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_sharedTerms.setEqualityEngine(ee);
}

void SharedSolverDistributed::preRegisterSharedInternal(TNode t)
{
  if (t.getKind() == kind::EQUAL)
  {
    // When sharing is enabled, we propagate from the shared terms manager also
    d_sharedTerms.addEqualityToPropagate(t);
  }
}

EqualityStatus SharedSolverDistributed::getEqualityStatus(TNode a, TNode b)
{
  // if we're using a shared terms database, ask its status if a and b are
  // shared.
  if (d_sharedTerms.isShared(a) && d_sharedTerms.isShared(b))
  {
    if (d_sharedTerms.areEqual(a, b))
    {
      return EQUALITY_TRUE_AND_PROPAGATED;
    }
    else if (d_sharedTerms.areDisequal(a, b))
    {
      return EQUALITY_FALSE_AND_PROPAGATED;
    }
  }
  // otherwise, ask the theory, which may depend on the uninterpreted sort owner
  TheoryId tid =
      Theory::theoryOf(a.getType(), d_env.getUninterpretedSortOwner());
  return d_te.theoryOf(tid)->getEqualityStatus(a, b);
}

TrustNode SharedSolverDistributed::explain(TNode literal, TheoryId id)
{
  TrustNode texp;
  if (id == THEORY_BUILTIN)
  {
    // explanation using the shared terms database
    texp = d_sharedTerms.explain(literal);
    Trace("shared-solver")
        << "\tTerm was propagated by THEORY_BUILTIN. Explanation: "
        << texp.getNode() << std::endl;
  }
  else
  {
    // By default, we ask the individual theory for the explanation.
    // It is possible that a centralized approach could preempt this.
    texp = d_te.theoryOf(id)->explain(literal);
    Trace("shared-solver") << "\tTerm was propagated by owner theory: " << id
                           << ". Explanation: " << texp.getNode() << std::endl;
  }
  return texp;
}

void SharedSolverDistributed::assertShared(TNode n, bool polarity, TNode reason)
{
  d_sharedTerms.assertShared(n, polarity, reason);
}

}  // namespace theory
}  // namespace cvc5::internal
