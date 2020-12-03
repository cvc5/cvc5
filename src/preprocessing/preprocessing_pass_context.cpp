/*********************                                                        */
/*! \file preprocessing_pass_context.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass context for passes
 **
 ** The preprocessing pass context for passes.
 **/

#include "preprocessing/preprocessing_pass_context.h"

#include "expr/node_algorithm.h"

namespace CVC4 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(
    SmtEngine* smt,
    RemoveTermFormulas* iteRemover,
    theory::booleans::CircuitPropagator* circuitPropagator,
    ProofNodeManager* pnm)
    : d_smt(smt),
      d_resourceManager(smt->getResourceManager()),
      d_iteRemover(iteRemover),
      d_topLevelSubstitutions(smt->getUserContext(), pnm),
      d_circuitPropagator(circuitPropagator),
      d_pnm(pnm),
      d_symsInAssertions(smt->getUserContext())
{
}

void PreprocessingPassContext::widenLogic(theory::TheoryId id)
{
  LogicRequest req(*d_smt);
  req.widenLogic(id);
}

theory::TrustSubstitutionMap&
PreprocessingPassContext::getTopLevelSubstitutions()
{
  return d_topLevelSubstitutions;
}

void PreprocessingPassContext::enableIntegers()
{
  LogicRequest req(*d_smt);
  req.enableIntegers();
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

ProofNodeManager* PreprocessingPassContext::getProofNodeManager()
{
  return d_pnm;
}

}  // namespace preprocessing
}  // namespace CVC4
