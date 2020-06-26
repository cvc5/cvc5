/*********************                                                        */
/*! \file proof_node_to_sexpr.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node to s-expression
 **/

#include "expr/proof_node_to_sexpr.h"

#include <iostream>

using namespace CVC4::kind;

namespace CVC4 {

ProofNodeToSExpr::ProofNodeToSExpr()
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TypeNode> types;
  d_argsMarker = nm->mkBoundVar(":args", nm->mkSExprType(types));
}

Node ProofNodeToSExpr::convertToSExpr(const ProofNode* pn)
{
  NodeManager* nm = NodeManager::currentNM();
  std::map<const ProofNode*, Node>::iterator it;
  std::vector<const ProofNode*> visit;
  std::vector<const ProofNode*> constructing;
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
      constructing.push_back(cur);
      visit.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        if (std::find(constructing.begin(), constructing.end(), cp.get())
            != constructing.end())
        {
          AlwaysAssert(false)
              << "ProofNodeToSExpr::convertToSExpr: cyclic proof!" << std::endl;
          return Node::null();
        }
        visit.push_back(cp.get());
      }
    }
    else if (it->second.isNull())
    {
      Assert(!constructing.empty());
      constructing.pop_back();
      std::vector<Node> children;
      // add proof rule
      children.push_back(getOrMkPfRuleVariable(cur->getRule()));
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
  std::vector<TypeNode> types;
  Node var = nm->mkBoundVar(ss.str(), nm->mkSExprType(types));
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
  std::vector<TypeNode> types;
  Node var = nm->mkBoundVar(ss.str(), nm->mkSExprType(types));
  d_nodeMap[n] = var;
  return var;
}

}  // namespace CVC4
