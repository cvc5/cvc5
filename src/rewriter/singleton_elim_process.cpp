/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database singleton elimination converter.
 */

#include "rewriter/singleton_elim_process.h"

namespace cvc5::internal {
namespace rewriter {

SingletonElimConverter::SingletonElimConverter(Env& env) : d_tpg(env, nullptr)
{
}

std::shared_ptr<ProofNode> SingletonElimConverter::convert(const Node& n, const Node& nse)
{
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction> visited;
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction>::iterator
      it;
  std::unordered_map<Node, Node>::iterator subsIt;
  std::vector<std::pair<TNode, TNode>> stack;
  stack.emplace_back(n, nse);
  std::pair<TNode, TNode> curr;
  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first==curr.second)
    {
      continue;
    }
    if (visited.find(curr)!=visited.end())
    {
      continue;
    }
    visited.insert(curr);
    if (curr.first.getKind()==Kind::APPLY_SINGLETON)
    {
      Node eq = curr.first.eqNode(curr.second);
      d_tpg.addRewriteStep(curr.first, curr.second, ProofRule::ACI_NORM, {}, {eq});
      stack.pop_back();
      continue;
    }
    // else recurse
    size_t nchild = curr.first.getNumChildren();
    Assert (curr.second.getNumChildren()==nchild);
    for (size_t i=0; i<nchild; i++)
    {
      stack.emplace_back(n[i], nse[i]);
    }
  }
  Node eq = n.eqNode(nse);
  return d_tpg.getProofFor(eq);
}


}  // namespace rewriter
}  // namespace cvc5::internal

