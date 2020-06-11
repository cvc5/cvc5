/*********************                                                        */
/*! \file proof_node_algorithm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node algorithm utilities
 **/

#include "expr/proof_node_algorithm.h"

namespace CVC4 {

void getFreeAssumptions(ProofNode * pn, std::vector<Node>& assump)
{
  std::map<Node, std::vector<ProofNode*>> amap;
  getFreeAssumptionsMap(pn, amap);
  for (const std::pair<const Node, std::vector<ProofNode*>>& p : amap)
  {
    assump.push_back(p.first);
  }
}

void getFreeAssumptionsMap(ProofNode * pn,
    std::map<Node, std::vector<ProofNode*>>& amap)
{
  // proof should not be cyclic
  // visited set false after preorder traversal, true after postorder traversal
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<ProofNode*> visit;
  // the current set of formulas bound by SCOPE
  std::unordered_set<Node, NodeHashFunction> currentScope;
  ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    const std::vector<Node>& cargs = cur->getArguments();
    if (it == visited.end())
    {
      visited[cur] = true;
      PfRule id = cur->getRule();
      if (id == PfRule::ASSUME)
      {
        Assert(cargs.size() == 1);
        Node f = cargs[0];
        if (currentScope.find(f) == currentScope.end())
        {
          amap[f].push_back(cur);
        }
      }
      else
      {
        if (id == PfRule::SCOPE)
        {
          // mark that its arguments are bound in the current scope
          for (const Node& a : cargs)
          {
            // should not have assumption shadowing
            Assert(currentScope.find(a) == currentScope.end());
            currentScope.insert(a);
          }
          // will need to unbind the variables below
          visited[cur] = false;
        }
        // The following loop cannot be merged with the loop above because the
        // same subproof
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        for (const std::shared_ptr<ProofNode>& cp : cs)
        {
          visit.push_back(cp.get());
        }
      }
    }
    else if (!it->second)
    {
      Assert(cur->getRule() == PfRule::SCOPE);
      // unbind its assumptions
      for (const Node& a : cargs)
      {
        currentScope.erase(a);
      }
    }
  } while (!visit.empty());
}

}  // namespace CVC4
