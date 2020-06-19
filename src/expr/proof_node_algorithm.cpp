/*********************                                                        */
/*! \file proof_node_algorithm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof node algorithm utilities
 **/

#include "expr/proof_node_algorithm.h"

namespace CVC4 {
namespace expr {

void getFreeAssumptions(ProofNode* pn, std::vector<Node>& assump)
{
  std::map<Node, std::vector<ProofNode*>> amap;
  getFreeAssumptionsMap(pn, amap);
  for (const std::pair<const Node, std::vector<ProofNode*>>& p : amap)
  {
    assump.push_back(p.first);
  }
}

void getFreeAssumptionsMap(ProofNode* pn,
                           std::map<Node, std::vector<ProofNode*>>& amap)
{
  // proof should not be cyclic
  // visited set false after preorder traversal, true after postorder traversal
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<ProofNode*> visit;
  // Maps a bound assumption to the number of bindings it is under
  // e.g. in (SCOPE (SCOPE (ASSUME x) (x y)) (y)), y would be mapped to 2 at
  // (ASSUME x), and x would be mapped to 1.
  //
  // This map is used to track which nodes are in scope while traversing the
  // DAG. The in-scope assumptions are keys in the map. They're removed when
  // their binding count drops to zero. Let's annotate the above example to
  // serve as an illustration:
  //
  //   (SCOPE0 (SCOPE1 (ASSUME x) (x y)) (y))
  //
  // This is how the map changes during the traversal:
  //   after  previsiting SCOPE0: { y: 1 }
  //   after  previsiting SCOPE1: { y: 2, x: 1 }
  //   at                 ASSUME: { y: 2, x: 1 } (so x is in scope!)
  //   after postvisiting SCOPE1: { y: 1 }
  //   after postvisiting SCOPE2: {}
  //
  std::unordered_map<Node, uint32_t, NodeHashFunction> scopeDepth;
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
        if (!scopeDepth.count(f))
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
            scopeDepth[a] += 1;
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
        auto scopeCt = scopeDepth.find(a);
        Assert(scopeCt != scopeDepth.end());
        scopeCt->second -= 1;
        if (scopeCt->second == 0)
        {
          scopeDepth.erase(scopeCt);
        }
      }
    }
  } while (!visit.empty());
}

}  // namespace expr
}  // namespace CVC4
