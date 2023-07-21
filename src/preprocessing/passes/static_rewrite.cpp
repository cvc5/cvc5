/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The StaticRewrite preprocessing pass.
 */

#include "preprocessing/passes/static_rewrite.h"

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/theory_engine.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

StaticRewrite::StaticRewrite(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "static-rewrite"){};

PreprocessingPassResult StaticRewrite::applyInternal(
    AssertionPipeline* assertions)
{
  // apply ppRewrite to all equalities in assertions
  for (std::size_t i = 0, size = assertions->size(); i < size; ++i)
  {
    Node assertion = (*assertions)[i];
    TrustNode trn = rewriteAssertion(assertion);
    if (!trn.isNull())
    {
      // replace based on the trust node
      assertions->replaceTrusted(i, trn);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

TrustNode StaticRewrite::rewriteAssertion(TNode n)
{
  NodeManager* nm = NodeManager::currentNM();
  TheoryEngine* te = d_preprocContext->getTheoryEngine();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node> rewrittenTo;
  std::unordered_map<TNode, Node>::iterator it;
  // to ensure all nodes are ref counted
  std::unordered_set<Node> keep;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur.getNumChildren()==0)
      {
        visit.pop_back();
        visited[cur] = cur;
      }
      else
      {
        visited[cur] = Node::null();
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      it = rewrittenTo.find(cur);
      if (it != rewrittenTo.end())
      {
        // rewritten form is the rewritten form of what it was rewritten to
        Assert(visited.find(it->second) != visited.end());
        visited[cur] = visited[it->second];
        visit.pop_back();
        continue;
      }
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
        keep.insert(ret);
      }
      bool wasRewritten = false;
      // For example, (= x y) ---> (and (>= x y) (<= x y))
      TrustNode trn = te->ppStaticRewrite(ret);
      // can make proof producing by using proof generator from trn
      if (!trn.isNull() && trn.getNode() != ret)
      {
        Trace("pp-rewrite-eq")
            << "Rewrite " << ret << " to " << trn.getNode() << std::endl;
        wasRewritten = true;
        Node retr = trn.getNode();
        keep.insert(retr);
        rewrittenTo[cur] = retr;
        rewrittenTo[ret] = retr;
        visit.push_back(retr);
      }
      if (!wasRewritten)
      {
        visit.pop_back();
        visited[cur] = ret;
      }
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
  // can make proof producing by providing a term conversion generator here
  return TrustNode::mkTrustRewrite(n, ret, nullptr);
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
