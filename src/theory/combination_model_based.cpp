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

#include "theory/model_manager.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "expr/node_trie.h"

namespace cvc5::internal {
namespace theory {

class RepInfo
{
public:
  Node d_baseRep;
  std::map<Node, std::vector<Node>> d_congTerms;
};

CombinationModelBased::CombinationModelBased(
    Env& env, TheoryEngine& te, const std::vector<Theory*>& paraTheories)
    : CombinationEngine(env, te, paraTheories)
{
}

CombinationModelBased::~CombinationModelBased() {}

void CombinationModelBased::resetModel()
{
  Trace("combination-mb") << "reset model" << std::endl;
  // already reset/built
  if (!logicInfo().isSharingEnabled())
  {
    d_mmanager->resetModel();
  }
}
  
void CombinationModelBased::combineTheories()
{
  Trace("combination-mb") << "CombinationModelBased::combineTheories" << std::endl;
  d_mmanager->resetModel();
  // go ahead and build the model now
  if (!d_mmanager->buildModel())
  {
    Trace("combination-mb") << "...failed build model" << std::endl;
    return;
  }
  std::map<Kind, NodeTrie> tries;
  // must double check 
  TheoryModel* tm = d_mmanager->getModel();
  eq::EqualityEngine* ee = tm->getEqualityEngine();
  eq::EqClassesIterator eqsi = eq::EqClassesIterator(ee);
  std::vector<Node> splits;
  bool hasConflict = false;
  std::map<Node, RepInfo> d_rinfo;
  std::unordered_set<Node> eqProcessed;
  while (!eqsi.isFinished())
  {
    Node r = (*eqsi);
    eq::EqClassIterator eqi = eq::EqClassIterator(r, ee);
    Node rcur = tm->getRepresentative(r);
    while (!eqi.isFinished())
    {
      Node n = (*eqi);
      ++eqi;
      if (n.getNumChildren()==0)
      {
        continue;
      }
      else if (n.isClosure())
      {
        continue;
      }
      Trace("combination-mb-terms") << "Check term: " << n << std::endl;
      if (false && !d_sharedSolver->isPreregistered(n))
      {
        Trace("combination-mb-terms") << "Not preregistered: " << n << std::endl;
        continue;
      }
      Kind k = n.getKind();
      std::vector<Node> reps;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        reps.push_back(n.getOperator());
      }
      else if (NodeManager::isNAryKind(k))
      {
        // don't do on variadic kinds, e.g. +, str.++
        continue;
      }
      NodeTrie& nt = tries[k];
      for (const Node& nc : n)
      {
        reps.emplace_back(tm->getRepresentative(nc));
      }
      Node ncrep = nt.addOrGetTerm(n, reps);
      if (ncrep==n)
      {
        continue;
      }
      RepInfo& ri = d_rinfo[ncrep];
      // initialize if necessary
      if (ri.d_congTerms.empty())
      {
        Node br = tm->getRepresentative(ncrep);
        ri.d_congTerms[br].push_back(ncrep);
      }
      ri.d_congTerms[rcur].push_back(n);
      for (const std::pair<const Node, std::vector<Node>>& cts : ri.d_congTerms)
      {
        for (const Node& nother : cts.second)
        {
          if (cts.first==rcur)
          {
            if (n==nother)
            {
              continue;
            }
            // even if made equal, we need to check arguments
            // TODO: could maybe skip if TRUE or TRUE_IN_MODEL
          }
          else
          {
            hasConflict = true;
          }
          Trace("combination-mb") << "Conflict: " << n << " vs " << nother << std::endl;
          Trace("combination-mb") << "...reps are " << rcur << " and " << cts.first << std::endl;
          Assert (nother.getNumChildren()==n.getNumChildren());
          for (size_t i=0, nchild=n.getNumChildren(); i<nchild; i++)
          {
            if (nother[i]==n[i])
            {
              // reflexive equality, not the issue
              continue;
            }
            // otherwise see if it is a pair of preregistered terms that are neither asserted
            // to be equal or disequal.
            Trace("combination-mb") << "Check argument " << nother[i] << " vs " << n[i] << std::endl;
            if (!d_sharedSolver->isShared(nother[i]) || !d_sharedSolver->isShared(n[i]))
            {
              Trace("combination-mb") << "...not shared" << std::endl;
              continue;
            }
            Node eq = nother[i].eqNode(n[i]);
            if (!eqProcessed.insert(eq).second)
            {
              // already processed
              continue;
            }
            // if the equality has already been asserted, don't split
            theory::EqualityStatus es = d_te.getEqualityStatus(nother[i], n[i]);
            Trace("combination-mb") << "...status is " << es << std::endl;
            if (es != EQUALITY_FALSE_IN_MODEL && es != EQUALITY_TRUE_IN_MODEL && es != EQUALITY_UNKNOWN)
            {
              // already asserted
              continue;
            }
            Trace("combination-mb") << "...split on " << eq << std::endl;
            splits.push_back(eq);
          }
        }
      }
    }
    ++eqsi;
  }
  if (splits.empty())
  {
    /*
    if (hasConflict)
    {
      Unhandled() << "Model has conflict but failed to find split";
    }
    */
    Trace("combination-mb") << "...success" << std::endl;
    return;
  }
  for (const Node& eq : splits)
  {
    TrustNode tsplit;
    if (isProofEnabled())
    {
      // make proof of splitting lemma
      tsplit = d_cmbsPg->mkTrustNodeSplit(eq);
    }
    else
    {
      Node split = eq.orNode(eq.notNode());
      tsplit = TrustNode::mkTrustLemma(split, nullptr);
    }
    d_sharedSolver->sendLemma(
        tsplit, TheoryId::THEORY_BUILTIN, InferenceId::COMBINATION_SPLIT_MB);
  }
}

bool CombinationModelBased::buildModel()
{
  // building the model happens as a separate step
  return d_mmanager->buildModel();
}

}  // namespace theory
}  // namespace cvc5::internal
