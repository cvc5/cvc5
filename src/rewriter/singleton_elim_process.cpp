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

#include "smt/env.h"
#include "proof/proof_node_manager.h"
#include "proof/proof_checker.h"

namespace cvc5::internal {
namespace rewriter {

SingletonElimConverter::SingletonElimConverter(Env& env) : EnvObj(env), d_tpg(env, nullptr)
{
}

std::shared_ptr<ProofNode> SingletonElimConverter::convert(const Node& n,
                                                           const Node& nse)
{
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
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
    Trace("selim-proc") << "Setup proof of " << curr.first
                        << " == " << curr.second << std::endl;
    stack.pop_back();
    if (curr.first == curr.second)
    {
      Trace("selim-proc") << "...already equal" << std::endl;
      continue;
    }
    if (visited.find(curr) != visited.end())
    {
      Trace("selim-proc") << "...already processed" << std::endl;
      continue;
    }
    visited.insert(curr);
    if (curr.first.getKind() == Kind::APPLY_SINGLETON)
    {
      Trace("selim-proc") << "...singleton eq" << std::endl;
      Node eq = curr.first.eqNode(curr.second);
      Node res = pc->checkDebug(ProofRule::ACI_NORM, {}, {eq}, Node::null(), "singleton elim");
      if (!res.isNull())
      {
        d_tpg.addRewriteStep(
            curr.first, curr.second, ProofRule::ACI_NORM, {}, {eq});
        continue;
      }
      res = pc->checkDebug(ProofRule::ARITH_POLY_NORM, {}, {eq}, Node::null(), "singleton elim");
      if (!res.isNull())
      {
        d_tpg.addRewriteStep(
            curr.first, curr.second, ProofRule::ARITH_POLY_NORM, {}, {eq});
        continue;
      }
      Assert(false) << "Unknown kind " << curr.first << " == " << curr.second;
      continue;
    }
    // else recurse
    size_t nchild = curr.first.getNumChildren();
    Trace("selim-proc") << "...recurse on " << nchild << " children" << std::endl;
    Assert(curr.second.getNumChildren() == nchild);
    for (size_t i = 0; i < nchild; i++)
    {
      stack.emplace_back(curr.first[i], curr.second[i]);
    }
  }
  Node eq = n.eqNode(nse);
  return d_tpg.getProofFor(eq);
}

}  // namespace rewriter
}  // namespace cvc5::internal
