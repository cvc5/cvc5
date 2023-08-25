/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node algorithm utilities.
 */

#include "proof/proof_node_algorithm.h"

#include "proof/proof_node.h"

namespace cvc5::internal {
namespace expr {

void getFreeAssumptions(ProofNode* pn, std::vector<Node>& assump)
{
  std::map<Node, std::vector<std::shared_ptr<ProofNode>>> amap;
  std::shared_ptr<ProofNode> spn = std::make_shared<ProofNode>(
      pn->getRule(), pn->getChildren(), pn->getArguments());
  getFreeAssumptionsMap(spn, amap);
  for (const std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>& p :
       amap)
  {
    assump.push_back(p.first);
  }
}

void getFreeAssumptionsMap(
    std::shared_ptr<ProofNode> pn,
    std::map<Node, std::vector<std::shared_ptr<ProofNode>>>& amap)
{
  // proof should not be cyclic
  // visited set false after preorder traversal, true after postorder traversal
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::vector<std::shared_ptr<ProofNode>> traversing;
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
  std::unordered_map<Node, uint32_t> scopeDepth;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur.get());
    const std::vector<Node>& cargs = cur->getArguments();
    if (it == visited.end())
    {
      PfRule id = cur->getRule();
      if (id == PfRule::ASSUME)
      {
        visited[cur.get()] = true;
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
        }
        // The following loop cannot be merged with the loop above because the
        // same subproof
        visited[cur.get()] = false;
        visit.push_back(cur);
        traversing.push_back(cur);
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        for (const std::shared_ptr<ProofNode>& cp : cs)
        {
          if (std::find(traversing.begin(), traversing.end(), cp)
              != traversing.end())
          {
            Unhandled() << "getFreeAssumptionsMap: cyclic proof! (use "
                           "--proof-check=eager)"
                        << std::endl;
          }
          visit.push_back(cp);
        }
      }
    }
    else if (!it->second)
    {
      Assert(!traversing.empty());
      traversing.pop_back();
      visited[cur.get()] = true;
      if (cur->getRule() == PfRule::SCOPE)
      {
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
    }
  } while (!visit.empty());
}

bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap)
{
  std::unordered_map<const ProofNode*, bool> visited;
  std::unordered_map<const ProofNode*, bool>::iterator it;
  std::vector<const ProofNode*> visit;
  visit.push_back(pn);
  bool foundAssumption = false;
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    // have we already computed?
    it = caMap.find(cur);
    if (it != caMap.end())
    {
      // if cached, we set found assumption to true if applicable and continue
      if (it->second)
      {
        foundAssumption = true;
      }
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      PfRule r = cur->getRule();
      if (r == PfRule::ASSUME)
      {
        visited[cur] = true;
        caMap[cur] = true;
        foundAssumption = true;
      }
      else if (!foundAssumption)
      {
        // if we haven't found an assumption yet, recurse. Otherwise, we will
        // not bother computing whether this subproof contains an assumption
        // since we know its parent already contains one by another child.
        visited[cur] = false;
        visit.push_back(cur);
        const std::vector<std::shared_ptr<ProofNode>>& children =
            cur->getChildren();
        for (const std::shared_ptr<ProofNode>& cp : children)
        {
          visit.push_back(cp.get());
        }
      }
    }
    else if (!it->second)
    {
      visited[cur] = true;
      // we contain an assumption if we've found an assumption in a child
      caMap[cur] = foundAssumption;
    }
  }
  return caMap[cur];
}

bool containsAssumption(const ProofNode* pn)
{
  std::unordered_map<const ProofNode*, bool> caMap;
  return containsAssumption(pn, caMap);
}

bool containsSubproof(ProofNode* pn, ProofNode* pnc)
{
  std::unordered_set<const ProofNode*> visited;
  return containsSubproof(pn, pnc, visited);
}

bool containsSubproof(ProofNode* pn,
                      ProofNode* pnc,
                      std::unordered_set<const ProofNode*>& visited)
{
  std::unordered_map<const ProofNode*, bool>::iterator it;
  std::vector<const ProofNode*> visit;
  visit.push_back(pn);
  const ProofNode* cur;
  while (!visit.empty())
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur == pnc)
      {
        return true;
      }
      const std::vector<std::shared_ptr<ProofNode>>& children =
          cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : children)
      {
        visit.push_back(cp.get());
      }
    }
  }
  return false;
}

}  // namespace expr
}  // namespace cvc5::internal
