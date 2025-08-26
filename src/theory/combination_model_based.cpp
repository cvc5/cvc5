/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a model-based approach for theory combination.
 */

#include "theory/combination_model_based.h"

#include "expr/node_trie.h"
#include "theory/model_manager.h"
#include "theory/shared_solver.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

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

void CombinationModelBased::combineTheories()
{
  Trace("combination-mb") << "CombinationModelBased::combineTheories"
                          << std::endl;
  // go ahead and build the model now
  if (!buildModel())
  {
    Trace("combination-mb") << "...failed build model" << std::endl;
    return;
  }
  // A trie for each kind of term, which is used to recognize congruent terms.
  std::map<Kind, NodeTrie> tries;
  // must double check
  TheoryModel* tm = d_mmanager->getModel();
  eq::EqualityEngine* ee = tm->getEqualityEngine();
  eq::EqClassesIterator eqsi = eq::EqClassesIterator(ee);
  std::vector<Node> splits;
  CVC5_UNUSED bool hasConflict = false;
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
      if (n.getNumChildren() == 0)
      {
        // skip atomic terms
        continue;
      }
      else if (n.isClosure())
      {
        // skip quantified formulas
        continue;
      }
      Trace("combination-mb-terms") << "Check term: " << n << std::endl;
      Kind k = n.getKind();
      std::vector<Node> reps;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        // APPLY_UF, APPLY_CONSTRUCTOR, etc. take operator into account
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
      if (ncrep == n)
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
      // Get the theory that owns the term. We will add splits based on
      // the status of its arguments in its equality engine. This handling
      // is based on Theory::addCarePairArgs.
      TheoryId tid = Theory::theoryOf(n);
      Theory* t = d_te.theoryOf(tid);
      eq::EqualityEngine* eet = t->getEqualityEngine();
      Assert(eet != nullptr);
      for (const std::pair<const Node, std::vector<Node>>& cts : ri.d_congTerms)
      {
        for (const Node& nother : cts.second)
        {
          if (cts.first == rcur)
          {
            if (n == nother)
            {
              continue;
            }
            // Even if made equal, we need to check arguments since we may
            // have merged two terms that a theory cannot make equal.
            // Note that it may be possible to check if this unintentional merge
            // of two terms is permissible, e.g if (f a) became equal to (f b)
            // but no theory has (f a) != (f b). We don't do this optimization
            // currently.
          }
          else
          {
            hasConflict = true;
          }
          Trace("combination-mb")
              << "Conflict: " << n << " vs " << nother << std::endl;
          Trace("combination-mb")
              << "...reps are " << rcur << " and " << cts.first << std::endl;
          Assert(nother.getNumChildren() == n.getNumChildren());
          Assert(eet != nullptr);
          for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
          {
            if (nother[i] == n[i])
            {
              // reflexive equality, not the issue
              continue;
            }
            Trace("combination-mb") << "Check argument " << nother[i] << " vs "
                                    << n[i] << std::endl;
            if (eet->isTriggerTerm(n[i], tid)
                && eet->isTriggerTerm(nother[i], tid)
                && !eet->areEqual(n[i], nother[i]))
            {
              TNode x_shared = eet->getTriggerTermRepresentative(n[i], tid);
              TNode y_shared =
                  eet->getTriggerTermRepresentative(nother[i], tid);
              Node eq = x_shared.eqNode(y_shared);
              if (!eqProcessed.insert(eq).second)
              {
                // already processed
                continue;
              }
              Trace("combination-mb") << "...split on " << eq << std::endl;
              splits.push_back(eq);
            }
          }
        }
      }
    }
    ++eqsi;
  }
  if (splits.empty())
  {
    Assert(!hasConflict) << "Model has conflict but failed to find split";
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
