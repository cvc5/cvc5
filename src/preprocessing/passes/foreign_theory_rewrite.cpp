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
  // first make sure the node is rewritten
  n = Rewriter::rewrite(n);
  // traverse the node
  for (TNode current :
       NodeDfsIterable(n, VisitOrder::POSTORDER, [this](TNode tn) {
         return d_cache.find(tn) != d_cache.end();
       }))
  {
    // the node is rewritten, and so GT, LT, LEQ
    // should be eliminated
    Assert(current.getKind() != kind::GT);
    Assert(current.getKind() != kind::LT);
    Assert(current.getKind() != kind::LEQ);

    // for GEQ, we check whether the node can be simplified
    if (current.getKind() == kind::GEQ)
    {
      Assert(d_cache.find(current[0]) != d_cache.end());
      Assert(d_cache.find(current[1]) != d_cache.end());
      // check if the node can be simplified to true
      if (theory::strings::ArithEntail::check(
              d_cache[current[0]], d_cache[current[1]], false))
      {
        d_cache[current] = NodeManager::currentNM()->mkConst<bool>(true);
      }
      else
      {
        d_cache[current] = current;
      }
    }
    else
    {
      // leaves are left unchanged
      if (current.getNumChildren() == 0)
      {
        d_cache[current] = current;
      }
      else
      {
        // compound nodes are reconstructed according to
        // the cache, with the simplified versions
        NodeBuilder<> builder(current.getKind());
        // special case for parameterized operators
        if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          builder << current.getOperator();
        }
        // add the children to the constructed node
        for (size_t i = 0; i < current.getNumChildren(); i++)
        {
          Assert(d_cache.find(current[i]) != d_cache.end());
          builder << d_cache[current[i]].get();
        }
        // store the reconstruction in the cache
        Node result = builder.constructNode();
        d_cache[current] = result;
      }
    }
  }
  // make sure the cache includes the input node
  Assert(d_cache.find(n) != d_cache.end());
  // return the simplified version
  return d_cache[n];
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
