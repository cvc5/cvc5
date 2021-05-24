/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node to s-expression.
 */

#include "proof/proof_node_to_sexpr.h"

#include <iostream>
#include <sstream>

#include "options/proof_options.h"
#include "proof/proof_node.h"

using namespace cvc5::kind;

namespace cvc5 {

ProofNodeToSExpr::ProofNodeToSExpr()
{
  NodeManager* nm = NodeManager::currentNM();
  d_conclusionMarker = nm->mkBoundVar(":conclusion", nm->sExprType());
  d_argsMarker = nm->mkBoundVar(":args", nm->sExprType());
}

Node ProofNodeToSExpr::convertToSExpr(const ProofNode* pn)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<const ProofNode*, Node>::iterator it;
  std::vector<const ProofNode*> visit;
  std::vector<const ProofNode*> traversing;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_pnMap.find(cur);

    if (it == d_pnMap.end())
    {
      d_pnMap[cur] = Node::null();
      traversing.push_back(cur);
      visit.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        if (std::find(traversing.begin(), traversing.end(), cp.get())
            != traversing.end())
        {
          Unhandled() << "ProofNodeToSExpr::convertToSExpr: cyclic proof! (use "
                         "--proof-eager-checking)"
                      << std::endl;
          return Node::null();
        }
        visit.push_back(cp.get());
      }
    }
    else if (it->second.isNull())
    {
      Assert(!traversing.empty());
      traversing.pop_back();
      std::vector<Node> children;
      // add proof rule
      children.push_back(getOrMkPfRuleVariable(cur->getRule()));
      if (options::proofPrintConclusion())
      {
        children.push_back(d_conclusionMarker);
        children.push_back(cur->getResult());
      }
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        it = d_pnMap.find(cp.get());
        Assert(it != d_pnMap.end());
        Assert(!it->second.isNull());
        children.push_back(it->second);
      }
      // add arguments
      const std::vector<Node>& args = cur->getArguments();
      if (!args.empty())
      {
        children.push_back(d_argsMarker);
        // needed to ensure builtin operators are not treated as operators
        // this can be the case for CONG where d_args may contain a builtin
        // operator
        std::vector<Node> argsSafe;
        for (const Node& a : args)
        {
          Node av = a;
          if (a.getNumChildren() == 0
              && NodeManager::operatorToKind(a) != UNDEFINED_KIND)
          {
            av = getOrMkNodeVariable(a);
          }
          argsSafe.push_back(av);
        }
        Node argsC = nm->mkNode(SEXPR, argsSafe);
        children.push_back(argsC);
      }
      d_pnMap[cur] = nm->mkNode(SEXPR, children);
    }
  } while (!visit.empty());
  Assert(d_pnMap.find(pn) != d_pnMap.end());
  Assert(!d_pnMap.find(pn)->second.isNull());
  return d_pnMap[pn];
}

Node ProofNodeToSExpr::getOrMkPfRuleVariable(PfRule r)
{
  std::map<PfRule, Node>::iterator it = d_pfrMap.find(r);
  if (it != d_pfrMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << r;
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
  d_pfrMap[r] = var;
  return var;
}

Node ProofNodeToSExpr::getOrMkNodeVariable(Node n)
{
  std::map<Node, Node>::iterator it = d_nodeMap.find(n);
  if (it != d_nodeMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << n;
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
  d_nodeMap[n] = var;
  return var;
}

}  // namespace cvc5
