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
}

Node DistinctElim::convert(TNode n)
{
  NodeManager* nm = nodeManager();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
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
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      bool childChanged = false;
      for (const Node& cn : cur)
      {
        Node ccn = visited[cn];
        Assert(!ccn.isNull());
        childChanged = childChanged || (cn != ccn);
        children.push_back(ccn);
      }
      Node ret = cur;
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // blast distinct if it is within the threshold (0 means no limit)
      if (ret.getKind() == Kind::DISTINCT
          && (d_threshold == 0 || ret.getNumChildren() <= d_threshold))
      {
        ret = theory::uf::TheoryUfRewriter::blastDistinct(nm, ret);
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
  return visited[n];
}

PreprocessingPassResult DistinctElim::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, nasserts = assertionsToPreprocess->size(); i < nasserts;
       ++i)
  {
    const Node& a = (*assertionsToPreprocess)[i];
    Node ar = convert(a);
    if (a == ar)
    {
      continue;
    }
    assertionsToPreprocess->replace(
        i, ar, nullptr, TrustId::PREPROCESS_DISTINCT_ELIM);
    assertionsToPreprocess->ensureRewritten(i);
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
