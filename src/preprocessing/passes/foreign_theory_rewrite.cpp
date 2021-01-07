/*********************                                                        */
/*! \file foreign_theory_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The foreign_theory_rewrite preprocessing pass
 **
 ** Simplifies nodes of one theory using rewrites from another.
 **/

#include "preprocessing/passes/foreign_theory_rewrite.h"

#include "expr/node_traversal.h"
#include "theory/strings/arith_entail.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;
ForeignTheoryRewrite::ForeignTheoryRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "foreign-theory-rewrite"),
      d_cache(preprocContext->getUserContext()){};


Node ForeignTheoryRewrite::simplify(Node n)
{
  vector<Node> toVisit;
  n = Rewriter::rewrite(n);
  toVisit.push_back(n);
  while (!toVisit.empty()) {
    Node current = toVisit.back();
    if (d_cache.find(current) == d_cache.end()) {
      // current is seen for the first time.
      // mark it by assigning a null node
      // and add its children to toVisit
      d_cache[current] = Node();
      toVisit.insert(toVisit.end(), current.begin(), current.end());
    } else if (d_cache[current].get().isNull()) {
      // current was seen but was not processed.
      // remove from toVisit
      toVisit.pop_back();
      // Reconstruct it with processed children,
      // process it, store the result in the cache, and add
      // the result to toVisit
      vector<Node> processedChildren;
      for (Node child : current) {
        Assert(d_cache.find(child) != d_cache.end());
        Assert(!d_cache[child].get().isNull());
        processedChildren.push_back(d_cache[child]);
      }
      Node reconstruction = reconstructNode(current, processedChildren);
      Node result = foreignRewrite(reconstruction);
      d_cache[current] = result;
      toVisit.push_back(result);
    } else {
       // current was already processed
       // remove from toVisit and skip
       toVisit.pop_back();
       continue;
    }
  }
  return d_cache[n];
}

Node ForeignTheoryRewrite::foreignRewrite(Node n) {
    // the node is rewritten, and so GT, LT, LEQ
    // should be eliminated
    Assert(n.getKind() != kind::GT);
    Assert(n.getKind() != kind::LT);
    Assert(n.getKind() != kind::LEQ);
    // for GEQ, we check whether the node can be simplified
    if (n.getKind() == kind::GEQ)
    {
      return rewriteStringsGeq(n);
    } else {
      return n;
    }
}

Node ForeignTheoryRewrite::rewriteStringsGeq(Node n)
{
  // check if the node can be simplified to true
  if (theory::strings::ArithEntail::check(n[0], n[1], false))
  {
    return NodeManager::currentNM()->mkConst<bool>(true);
  }
  else
  {
    return n;
  }
}

Node ForeignTheoryRewrite::reconstructNode(Node originalNode, vector<Node> newChildren) {
      if (originalNode.getNumChildren() == 0) {
        Assert(newChildren.empty());
        return originalNode;
      } else {
        kind::Kind_t k = originalNode.getKind();
        NodeBuilder<> builder(k);
        if (originalNode.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          builder << originalNode.getOperator();
        }
        for (Node child : newChildren)
        {
          builder << child;
        }
        return builder.constructNode();
      }
}

PreprocessingPassResult ForeignTheoryRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite(simplify((*assertionsToPreprocess)[i])));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
