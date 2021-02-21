/*********************                                                        */
/*! \file theory_rewrite_eq.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The TheoryRewriteEq preprocessing pass
 **/

#include "preprocessing/passes/theory_rewrite_eq.h"

#include "theory/theory_engine.h"

using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {

TheoryRewriteEq::TheoryRewriteEq(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "theory-rewrite-eq"){};

PreprocessingPassResult TheoryRewriteEq::applyInternal(
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

theory::TrustNode TheoryRewriteEq::rewriteAssertion(TNode n)
{
  NodeManager* nm = NodeManager::currentNM();
  TheoryEngine* te = d_preprocContext->getTheoryEngine();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur.getNumChildren()==0)
      {
        visited[cur] = cur;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
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
      }
      if (ret.getKind() == kind::EQUAL && !ret[0].getType().isBoolean())
      {
        // For example, (= x y) ---> (and (>= x y) (<= x y))
        theory::TrustNode trn = te->ppRewriteEquality(ret);
        // can make proof producing by using proof generator from trn
        ret = trn.isNull() ? Node(ret) : trn.getNode();
      }
      visited[cur] = ret;
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
}  // namespace CVC4
