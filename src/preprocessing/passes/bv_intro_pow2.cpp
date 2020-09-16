/*********************                                                        */
/*! \file bv_intro_pow2.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BvIntroPow2 preprocessing pass
 **
 ** Traverses the formula and applies the IsPowerOfTwo rewrite rule. This
 ** preprocessing pass is particularly useful on QF_BV/pspace benchmarks and
 ** can be enabled via option `--bv-intro-pow2`.
 **/

#include "preprocessing/passes/bv_intro_pow2.h"

#include <unordered_map>

#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;
using namespace CVC4::theory;

namespace {

Node pow2Rewrite(Node node, NodeMap& cache)
{
  NodeMap::const_iterator ci = cache.find(node);
  if (ci != cache.end())
  {
    Node incache = (*ci).second;
    return incache.isNull() ? node : incache;
  }

  Node res = Node::null();
  switch (node.getKind())
  {
    case kind::AND:
    {
      bool changed = false;
      std::vector<Node> children;
      for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
      {
        Node child = node[i];
        Node found = pow2Rewrite(child, cache);
        changed = changed || (child != found);
        children.push_back(found);
      }
      if (changed)
      {
        res = NodeManager::currentNM()->mkNode(kind::AND, children);
      }
    }
    break;

    case kind::EQUAL:
      if (node[0].getType().isBitVector()
          && theory::bv::RewriteRule<theory::bv::IsPowerOfTwo>::applies(node))
      {
        res = theory::bv::RewriteRule<theory::bv::IsPowerOfTwo>::run<false>(node);
      }
      break;
    default: break;
  }

  cache.insert(std::make_pair(node, res));
  return res.isNull() ? node : res;
}

}  // namespace

BvIntroPow2::BvIntroPow2(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-intro-pow2"){};

PreprocessingPassResult BvIntroPow2::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node cur = (*assertionsToPreprocess)[i];
    Node res = pow2Rewrite(cur, cache);
    if (res != cur)
    {
      res = Rewriter::rewrite(res);
      assertionsToPreprocess->replace(i, res);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */
