/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node algorithm utilities.
 */

#include "proof/proof_node_algorithm.h"

#include "proof/proof_node.h"
#include "proof/proof_rule_checker.h"

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
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
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
      visited.insert(cur.get());
      ProofRule id = cur->getRule();
      if (id == ProofRule::ASSUME)
      {
        Assert(cargs.size() == 1);
        Node f = cargs[0];
        amap[f].push_back(cur);
      }
      else
      {
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        if (id == ProofRule::SCOPE)
        {
          // make a recursive call, which is bound in depth by the number of
          // nested SCOPE (never expected to be more than 1 or 2).
          std::map<Node, std::vector<std::shared_ptr<ProofNode>>> amapTmp;
          expr::getFreeAssumptionsMap(cs[0], amapTmp);
          for (std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>&
                   a : amapTmp)
          {
            if (std::find(cargs.begin(), cargs.end(), a.first) == cargs.end())
            {
              std::vector<std::shared_ptr<ProofNode>>& pfs = amap[a.first];
              pfs.insert(pfs.end(), a.second.begin(), a.second.end());
            }
          }
          continue;
        }
        // traverse on children
        visit.insert(visit.end(), cs.begin(), cs.end());
      }
    }
  } while (!visit.empty());
}

void getSubproofRule(std::shared_ptr<ProofNode> pn,
                     ProofRule r,
                     std::vector<std::shared_ptr<ProofNode>>& pfs)
{
  // proof should not be cyclic
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur.get());
    if (it == visited.end())
    {
      visited.insert(cur.get());
      if (cur->getRule() == r)
      {
        pfs.push_back(cur);
      }
      else
      {
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        // traverse on children
        visit.insert(visit.end(), cs.begin(), cs.end());
      }
    }
  } while (!visit.empty());
}

bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap,
                        const std::unordered_set<Node>& allowed)
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
      ProofRule r = cur->getRule();
      if (r == ProofRule::ASSUME)
      {
        bool ret = allowed.find(cur->getArguments()[0]) == allowed.end();
        visited[cur] = ret;
        caMap[cur] = ret;
        foundAssumption = ret;
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
bool containsAssumption(const ProofNode* pn,
                        std::unordered_map<const ProofNode*, bool>& caMap)
{
  std::unordered_set<Node> allowed;
  return containsAssumption(pn, caMap, allowed);
}

bool containsAssumption(const ProofNode* pn)
{
  std::unordered_map<const ProofNode*, bool> caMap;
  std::unordered_set<Node> allowed;
  return containsAssumption(pn, caMap, allowed);
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

ProofRule getCongRule(const Node& n, std::vector<Node>& args)
{
  Kind k = n.getKind();
  ProofRule r = ProofRule::CONG;
  switch (k)
  {
    case Kind::APPLY_UF:
    case Kind::DISTINCT:
    case Kind::FLOATINGPOINT_LT:
    case Kind::FLOATINGPOINT_LEQ:
    case Kind::FLOATINGPOINT_GT:
    case Kind::FLOATINGPOINT_GEQ:
    case Kind::NULLABLE_LIFT:
    case Kind::APPLY_INDEXED_SYMBOLIC:
      // takes arbitrary but we use CONG
      break;
    case Kind::HO_APPLY:
      // Use HO_CONG, since HO_APPLY is encoded as native function application.
      // This requires no arguments so we return.
      r = ProofRule::HO_CONG;
      break;
    case Kind::APPLY_CONSTRUCTOR:
      // tuples are n-ary, others are fixed
      r = n.getType().isTuple() ? ProofRule::NARY_CONG : ProofRule::CONG;
      break;
    default:
      if (NodeManager::isNAryKind(k))
      {
        // n-ary operators that are not handled as exceptions above use
        // NARY_CONG
        r = ProofRule::NARY_CONG;
      }
      break;
  }
  // Add the arguments
  args.push_back(ProofRuleChecker::mkKindNode(k));
  if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
  {
    args.push_back(n.getOperator());
  }
  else if (n.isClosure())
  {
    // bound variable list is an argument for closure over congruence
    args.push_back(n[0]);
  }
  return r;
}

}  // namespace expr
}  // namespace cvc5::internal
