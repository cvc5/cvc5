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
 * The default model constructor for strings
 */

#include "theory/strings/model_cons_default.h"

#include "theory/strings/core_solver.h"
#include "theory/strings/solver_state.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

ModelConsDefault::ModelConsDefault(Env& env,
                                   SolverState& state,
                                   CoreSolver& csolver)
    : ModelCons(env), d_state(state), d_csolver(csolver)
{
}

void ModelConsDefault::getStringRepresentativesFrom(
    const std::set<Node>& termSet,
    std::unordered_set<TypeNode>& repTypes,
    std::map<TypeNode, std::unordered_set<Node>>& repSet,
    std::vector<Node>& auxEq)
{
  for (const Node& s : termSet)
  {
    TypeNode tn = s.getType();
    if (tn.isStringLike())
    {
      Node r = d_state.getRepresentative(s);
      repSet[tn].insert(r);
      repTypes.insert(tn);
    }
  }
}

void ModelConsDefault::separateByLength(const std::vector<Node>& ns,
                                        std::vector<std::vector<Node>>& cols,
                                        std::vector<Node>& lts)
{
  d_state.separateByLength(ns, cols, lts);
  // look up the values of each length term
  Valuation& val = d_state.getValuation();
  for (Node& ll : lts)
  {
    if (!ll.isConst())
    {
      ll = val.getCandidateModelValue(ll);
    }
  }
}

std::vector<Node> ModelConsDefault::getNormalForm(Node n)
{
  return d_csolver.getNormalForm(n).d_nf;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
