/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PB-blasting solver.
 */

#include "theory/bv/bv_solver_pb.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

BVSolverPseudoBoolean::BVSolverPseudoBoolean(Env& env,
                                             TheoryState* state,
                                             TheoryInferenceManager& inferMgr)
    : BVSolver(env, *state, inferMgr),
      d_pbSolver(nullptr, [](PseudoBooleanSolver*) {}),
      d_pbBlaster(nullptr, [](PseudoBooleanBlaster*) {}),
      d_facts(context()),
      d_assumptions(context())
{
  Unimplemented();
}

bool BVSolverPseudoBoolean::needsEqualityEngine(EeSetupInfo& esi)
{
  Unimplemented();
}

void BVSolverPseudoBoolean::preRegisterTerm(TNode n) { Unimplemented(); }

void BVSolverPseudoBoolean::postCheck(Theory::Effort level) { Unimplemented(); }

bool BVSolverPseudoBoolean::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Unimplemented();
}

TrustNode BVSolverPseudoBoolean::explain(TNode n) { Unimplemented(); }

std::string BVSolverPseudoBoolean::identify() const { Unimplemented(); }

void BVSolverPseudoBoolean::computeRelevantTerms(std::set<Node>& termSet)
{
  Unimplemented();
}

bool BVSolverPseudoBoolean::collectModelValues(TheoryModel* m,
                                               const std::set<Node>& termSet)
{
  Unimplemented();
}

Node BVSolverPseudoBoolean::getValue(TNode node, bool initialize)
{
  Unimplemented();
}

void BVSolverPseudoBoolean::initPbSolver() { Unimplemented(); }

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
