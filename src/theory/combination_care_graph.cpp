/*********************                                                        */
/*! \file combination_care_graph.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "theory/combination_care_graph.h"

#include "expr/node_visitor.h"
#include "prop/prop_engine.h"
#include "theory/care_graph.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

CombinationCareGraph::CombinationCareGraph(
    TheoryEngine& te,
    const std::vector<Theory*>& paraTheories,
    ProofNodeManager* pnm)
    : CombinationEngine(te, paraTheories, pnm)
{
}

CombinationCareGraph::~CombinationCareGraph() {}

void CombinationCareGraph::combineTheories()
{
  Trace("combineTheories") << "TheoryEngine::combineTheories()" << std::endl;

  // Care graph we'll be building
  CareGraph careGraph;

  // get the care graph from the parametric theories
  for (Theory* t : d_paraTheories)
  {
    t->getCareGraph(&careGraph);
  }

  Trace("combineTheories")
      << "TheoryEngine::combineTheories(): care graph size = "
      << careGraph.size() << std::endl;

  // Now add splitters for the ones we are interested in
  prop::PropEngine* propEngine = d_te.getPropEngine();
  for (const CarePair& carePair : careGraph)
  {
    Debug("combineTheories")
        << "TheoryEngine::combineTheories(): checking " << carePair.d_a << " = "
        << carePair.d_b << " from " << carePair.d_theory << std::endl;

    // The equality in question (order for no repetition)
    Node equality = carePair.d_a.eqNode(carePair.d_b);

    // We need to split on it
    Debug("combineTheories")
        << "TheoryEngine::combineTheories(): requesting a split " << std::endl;

    TrustNode tsplit;
    if (isProofEnabled())
    {
      // make proof of splitting lemma
      tsplit = d_cmbsPg->mkTrustNodeSplit(equality);
    }
    else
    {
      Node split = equality.orNode(equality.notNode());
      tsplit = TrustNode::mkTrustLemma(split, nullptr);
    }
    sendLemma(tsplit, carePair.d_theory);

    // Could check the equality status here:
    //   EqualityStatus es = getEqualityStatus(carePair.d_a, carePair.d_b);
    // and only require true phase below if:
    //   es == EQUALITY_TRUE || es == EQUALITY_TRUE_IN_MODEL
    // and require false phase below if:
    //   es == EQUALITY_FALSE_IN_MODEL
    // This is supposed to force preference to follow what the theory models
    // already have but it doesn't seem to make a big difference - need to
    // explore more -Clark
    Node e = d_valuation.ensureLiteral(equality);
    propEngine->requirePhase(e, true);
  }
}

bool CombinationCareGraph::buildModel()
{
  // building the model happens as a separate step
  return d_mmanager->buildModel();
}

}  // namespace theory
}  // namespace CVC4
