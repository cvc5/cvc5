/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The foreign_theory_rewrite preprocessing pass.
 *
 * Simplifies nodes of one theory using rewrites from another.
 */

#include "preprocessing/passes/foreign_theory_rewrite.h"

#include "expr/node_traversal.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

ForeignTheoryRewriter::ForeignTheoryRewriter(Env& env)
    : EnvObj(env), d_cache(userContext())
{
}

Node ForeignTheoryRewriter::simplify(Node n)
{
  std::vector<Node> toVisit;
  n = rewrite(n);
  toVisit.push_back(n);
  // traverse n and rewrite until fixpoint
  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    // split according to three cases:
    // 1. We have not visited this node
    // 2. We visited it but did not process it
    // 3. We already processed and cached the node
    if (d_cache.find(current) == d_cache.end())
    {
      // current is seen for the first time.
      // mark it by assigning a null node
      // and add its children to toVisit
      d_cache[current] = Node();
      toVisit.insert(toVisit.end(), current.begin(), current.end());
    }
    else if (d_cache[current].get().isNull())
    {
      // current was seen but was not processed.
      // (a) remove from toVisit
      toVisit.pop_back();
      // (b) Reconstruct it with processed children
      std::vector<Node> processedChildren;
      for (Node child : current)
      {
        Assert(d_cache.find(child) != d_cache.end());
        Assert(!d_cache[child].get().isNull());
        processedChildren.push_back(d_cache[child]);
      }
      Node reconstruction = reconstructNode(current, processedChildren);
      // (c) process the node and store the result in the cache
      Node result = foreignRewrite(reconstruction);
      d_cache[current] = result;
      // (d) add the result to toVisit, unless it is the same as current
      if (current != result)
      {
        toVisit.push_back(result);
      }
    }
    else
    {
      // current was already processed
      // remove from toVisit and skip
      toVisit.pop_back();
    }
  }
  return d_cache[n];
}

Node ForeignTheoryRewriter::foreignRewrite(Node n)
{
  // n is a rewritten node, and so GT, LT, LEQ
  // should have been eliminated
  Assert(n.getKind() != kind::GT);
  Assert(n.getKind() != kind::LT);
  Assert(n.getKind() != kind::LEQ);
  // apply rewrites according to the structure of n
  if (n.getKind() == kind::GEQ)
  {
    return rewriteStringsGeq(n);
  }
  return n;
}

Node ForeignTheoryRewriter::rewriteStringsGeq(Node n)
{
  theory::strings::ArithEntail ae(d_env.getRewriter());
  // check if the node can be simplified to true
  if (ae.check(n[0], n[1], false))
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  return n;
}

Node ForeignTheoryRewriter::reconstructNode(Node originalNode,
                                            std::vector<Node> newChildren)
{
  // Nodes with no children are reconstructed to themselves
  if (originalNode.getNumChildren() == 0)
  {
    Assert(newChildren.empty());
    return originalNode;
  }
  // re-build the node with the same kind and new children
  kind::Kind_t k = originalNode.getKind();
  NodeBuilder builder(k);
  // special case for parameterized nodes
  if (originalNode.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << originalNode.getOperator();
  }
  // reconstruction
  for (Node child : newChildren)
  {
    builder << child;
  }
  return builder.constructNode();
}

ForeignTheoryRewrite::ForeignTheoryRewrite(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "foreign-theory-rewrite"),
      d_ftr(preprocContext->getEnv())
{
}

PreprocessingPassResult ForeignTheoryRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, nasserts = assertionsToPreprocess->size(); i < nasserts;
       ++i)
  {
    assertionsToPreprocess->replace(
        i, rewrite(d_ftr.simplify((*assertionsToPreprocess)[i])));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
