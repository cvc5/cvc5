/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The NlExtPurify preprocessing pass.
 *
 * Purifies non-linear terms.
 */

#include "preprocessing/passes/nl_ext_purify.h"

#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;

Node NlExtPurify::purifyNlTerms(TNode n,
                                NodeMap& cache,
                                NodeMap& bcache,
                                std::vector<Node>& var_eq,
                                bool beneathMult)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  if (beneathMult)
  {
    NodeMap::iterator find = bcache.find(n);
    if (find != bcache.end())
    {
      return (*find).second;
    }
  }
  else
  {
    NodeMap::iterator find = cache.find(n);
    if (find != cache.end())
    {
      return (*find).second;
    }
  }
  if (n.isClosure())
  {
    // don't traverse quantified formulas
    return n;
  }
  Node ret = n;
  if (n.getNumChildren() > 0)
  {
    if (beneathMult && (n.getKind() == kind::ADD || n.getKind() == kind::SUB))
    {
      // don't do it if it rewrites to a constant
      Node nr = rewrite(n);
      if (nr.isConst())
      {
        // return the rewritten constant
        ret = nr;
      }
      else
      {
        // new variable
        ret = sm->mkDummySkolem("__purifyNl_var",
                                n.getType(),
                                "Variable introduced in purifyNl pass");
        Node np = purifyNlTerms(n, cache, bcache, var_eq, false);
        var_eq.push_back(np.eqNode(ret));
        Trace("nl-ext-purify") << "Purify : " << ret << " -> " << np
                               << std::endl;
      }
    }
    else
    {
      bool beneathMultNew = beneathMult || n.getKind() == kind::MULT;
      bool childChanged = false;
      std::vector<Node> children;
      for (unsigned i = 0, size = n.getNumChildren(); i < size; ++i)
      {
        Node nc = purifyNlTerms(n[i], cache, bcache, var_eq, beneathMultNew);
        childChanged = childChanged || nc != n[i];
        children.push_back(nc);
      }
      if (childChanged)
      {
        ret = nm->mkNode(n.getKind(), children);
      }
    }
  }
  if (beneathMult)
  {
    bcache[n] = ret;
  }
  else
  {
    cache[n] = ret;
  }
  return ret;
}

NlExtPurify::NlExtPurify(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "nl-ext-purify"){};

PreprocessingPassResult NlExtPurify::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, Node> cache;
  unordered_map<Node, Node> bcache;
  std::vector<Node> var_eq;
  unsigned size = assertionsToPreprocess->size();
  for (unsigned i = 0; i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    Node ap = purifyNlTerms(a, cache, bcache, var_eq);
    if (a != ap)
    {
      assertionsToPreprocess->replace(i, ap);
      Trace("nl-ext-purify")
          << "Purify : " << a << " -> " << (*assertionsToPreprocess)[i] << "\n";
    }
  }
  if (!var_eq.empty())
  {
    unsigned lastIndex = size - 1;
    Node veq = NodeManager::currentNM()->mkAnd(var_eq);
    assertionsToPreprocess->conjoin(lastIndex, veq);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
