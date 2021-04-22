/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The preprocessing pass context for passes.
 */

#include "preprocessing/preprocessing_pass_context.h"

#include "expr/node_algorithm.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(
    SmtEngine* smt,
    theory::booleans::CircuitPropagator* circuitPropagator,
    ProofNodeManager* pnm)
    : d_smt(smt),
      d_resourceManager(smt->getResourceManager()),
      d_topLevelSubstitutions(smt->getUserContext(), pnm),
      d_circuitPropagator(circuitPropagator),
      d_pnm(pnm),
      d_symsInAssertions(smt->getUserContext())
{
}

theory::TrustSubstitutionMap&
PreprocessingPassContext::getTopLevelSubstitutions()
{
  return d_topLevelSubstitutions;
}

void PreprocessingPassContext::recordSymbolsInAssertions(
    const std::vector<Node>& assertions)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<Node, NodeHashFunction> syms;
  for (TNode cn : assertions)
  {
    expr::getSymbols(cn, syms, visited);
  }
  for (const Node& s : syms)
  {
    d_symsInAssertions.insert(s);
  }
}

void PreprocessingPassContext::addModelSubstitution(const Node& lhs,
                                                    const Node& rhs)
{
  getTheoryEngine()->getModel()->addSubstitution(
      lhs, d_smt->expandDefinitions(rhs, false));
}

void PreprocessingPassContext::addSubstitution(const Node& lhs,
                                               const Node& rhs,
                                               ProofGenerator* pg)
{
  d_topLevelSubstitutions.addSubstitution(lhs, rhs, pg);
  // also add as a model substitution
  addModelSubstitution(lhs, rhs);
}

ProofNodeManager* PreprocessingPassContext::getProofNodeManager()
{
  return d_pnm;
}

}  // namespace preprocessing
}  // namespace cvc5
