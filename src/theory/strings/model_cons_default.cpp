/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
    CVC5_UNUSED std::vector<Node>& auxEq)
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

void ModelConsDefault::separateByLength(TheoryModel* m,
                                        const std::vector<Node>& ns,
                                        std::vector<std::vector<Node>>& cols,
                                        std::vector<Node>& lts)
{
  d_state.separateByLength(ns, cols, lts);
  // look up the values of each length term
  for (Node& ll : lts)
  {
    if (ll.isNull() || ll.isConst())
    {
      continue;
    }
    // Previously we called Valuation::getCandidateModelValue for this purpose,
    // which relied on the arithmetic theory solver to confirm the value of ll.
    // However, it is better to simply ask the model object (which the
    // arithmetic solver has already populated for us). Moreover this
    // avoids assertion failures when using ee-mode=central.
    if (m->hasTerm(ll))
    {
      ll = m->getRepresentative(ll);
      continue;
    }
    // Note that ll is the representative of the length in the equality engine
    // of this theory, which the model may not know. This is possible when
    // using ee-mode=central, where the representative may e.g. be a polynomial
    // (+ (str.len x) (str.len y)) that the arithmetic solver treats as an
    // auxiliary term and thus does not assign a value to. In this case, we
    // look for a term in the equivalence class of ll whose value is known to
    // the model, e.g. the length term (str.len z) itself.
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    eq::EqClassIterator eqc_i = eq::EqClassIterator(ll, ee);
    while (!eqc_i.isFinished())
    {
      Node n = *eqc_i;
      if (m->hasTerm(n))
      {
        Node nv = m->getRepresentative(n);
        if (nv.isConst())
        {
          ll = nv;
          break;
        }
      }
      ++eqc_i;
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
