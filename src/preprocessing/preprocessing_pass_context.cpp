/*********************                                                        */
/*! \file preprocessing_pass_context.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass context for passes
 **
 ** The preprocessing pass context for passes.
 **/

#include "preprocessing_pass_context.h"

#include "expr/node_algorithm.h"

namespace CVC4 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(
    SmtEngine* smt,
    ResourceManager* resourceManager,
    RemoveTermFormulas* iteRemover,
    theory::booleans::CircuitPropagator* circuitPropagator)
    : d_smt(smt),
      d_resourceManager(resourceManager),
      d_iteRemover(iteRemover),
      d_topLevelSubstitutions(smt->d_userContext),
      d_circuitPropagator(circuitPropagator),
      d_symsInAssertions(smt->d_userContext)
{
}

void PreprocessingPassContext::widenLogic(theory::TheoryId id)
{
  LogicRequest req(*d_smt);
  req.widenLogic(id);
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

}  // namespace preprocessing
}  // namespace CVC4
