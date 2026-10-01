/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The distinct_elim preprocessing pass.
 *
 * Eagerly eliminates (blasts) distinct terms into pairwise disequalities,
 * based on a configurable threshold on the number of children.
 */

#include "preprocessing/passes/distinct_elim.h"

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/uf/theory_uf_rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

DistinctElim::DistinctElim(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "distinct-elim"),
      d_threshold(options().smt.distinctElimThreshold)
{
  if (options().smt.produceProofs)
  {
    d_tpg.reset(new TConvProofGenerator(d_env,
                                        userContext(),
                                        TConvPolicy::FIXPOINT,
                                        TConvCachePolicy::NEVER,
                                        "DistinctElim::tpg"));
  }
}

PreprocessingPassResult DistinctElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, nasserts = assertionsToPreprocess->size(); i < nasserts;
       ++i)
  {
    TrustNode trn = eliminate((*assertionsToPreprocess)[i]);
    if (trn.isNull())
    {
      continue;
    }
    assertionsToPreprocess->replaceTrusted(i, trn);
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

TrustNode DistinctElim::eliminate(TNode n)
{
  NodeManager* nm = nodeManager();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  // to ensure all intermediate nodes are ref counted
  std::unordered_set<Node> keep;
  std::vector<TNode> visit;
  visit.push_back(n);
  do
  {
    TNode cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      // reconstruct with processed children
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        Assert(visited.find(cn) != visited.end());
        Assert(!visited[cn].isNull());
        childChanged = childChanged || cn != visited[cn];
        children.push_back(visited[cn]);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
        keep.insert(ret);
      }
      // blast distinct if it is within the threshold (0 means no limit)
      if (ret.getKind() == Kind::DISTINCT
          && (d_threshold == 0 || ret.getNumChildren() <= d_threshold))
      {
        Node blasted = theory::uf::TheoryUfRewriter::blastDistinct(nm, ret);
        keep.insert(blasted);
        if (d_tpg != nullptr)
        {
          // justify (= ret blasted) via the DISTINCT_ELIM proof rewrite rule
          d_tpg->addTheoryRewriteStep(
              ret, blasted, ProofRewriteRule::DISTINCT_ELIM);
        }
        ret = blasted;
      }
      visited[cur] = ret;
      visit.pop_back();
    }
    else
    {
      visit.pop_back();
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Node ret = visited[n];
  if (ret == n)
  {
    return TrustNode::null();
  }
  // use the term conversion proof generator if it exists
  return TrustNode::mkTrustRewrite(n, ret, d_tpg.get());
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
