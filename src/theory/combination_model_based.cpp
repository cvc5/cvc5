/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a care graph based approach for theory combination.
 */

#include "theory/combination_model_based.h"

#include "expr/node_visitor.h"
#include "prop/prop_engine.h"
#include "theory/care_graph.h"
#include "theory/model_manager.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace theory {

CombinationModelBased::CombinationModelBased(
    Env& env, TheoryEngine& te, const std::vector<Theory*>& paraTheories)
    : CombinationEngine(env, te, paraTheories)
{
}

CombinationModelBased::~CombinationModelBased() {}

void CombinationModelBased::combineTheories()
{
  std::vector<Node> conflicts;
  if (!d_mmanager->buildModel())
  {
    for (const Node& c : conflicts)
    {
      TrustNode tc = TrustNode::mkTrustLemma(c, nullptr);
      d_sharedSolver->sendLemma(
          tc, TheoryId::THEORY_BUILTIN, InferenceId::COMBINATION_SPLIT);
    }
  }
}

bool CombinationModelBased::buildModel()
{
  // building the model happens as a separate step
  return d_mmanager->buildModel();
}

}  // namespace theory
}  // namespace cvc5::internal
