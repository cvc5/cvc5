/*********************                                                        */
/*! \file nl_ext_purify.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The NlExtPurify preprocessing pass
 **
 ** Purifies non-linear terms
 **/

#include "preprocessing/passes/nl_ext_purify.h"


namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

Node NlExtPurify::purifyNlTerms(TNode n,
                                NodeMap& cache,
                                NodeMap& bcache,
                                std::vector<Node>& var_eq,
                                bool beneathMult)
{
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
    if (beneathMult
        && (n.getKind() == kind::PLUS || n.getKind() == kind::MINUS))
    {
      // don't do it if it rewrites to a constant
      Node nr = Rewriter::rewrite(n);
      if (nr.isConst())
      {
        // return the rewritten constant
        ret = nr;
      }
      else
      {
        // new variable
        ret = NodeManager::currentNM()->mkSkolem(
            "__purifyNl_var",
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
        ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
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
  unordered_map<Node, Node, NodeHashFunction> cache;
  unordered_map<Node, Node, NodeHashFunction> bcache;
  std::vector<Node> var_eq;
  unsigned size = assertionsToPreprocess->size();
  for (unsigned i = 0; i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    assertionsToPreprocess->replace(i, purifyNlTerms(a, cache, bcache, var_eq));
    Trace("nl-ext-purify") << "Purify : " << a << " -> "
                           << (*assertionsToPreprocess)[i] << "\n";
  }
  if (!var_eq.empty())
  {
    unsigned lastIndex = size - 1;
    var_eq.insert(var_eq.begin(), (*assertionsToPreprocess)[lastIndex]);
    assertionsToPreprocess->replace(
        lastIndex, NodeManager::currentNM()->mkNode(kind::AND, var_eq));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
