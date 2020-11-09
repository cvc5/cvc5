/*********************                                                        */
/*! \file letify.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for computing letification
 **/

#include "proof/lfsc/letify.h"

namespace CVC4 {
namespace proof {

Node Letify::convert(Node n,
                     const std::map<Node, uint32_t>& letMap,
                     const std::string& prefix)
{
  if (letMap.empty())
  {
    return n;
  }
  std::map<Node, uint32_t>::const_iterator itl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      itl = letMap.find(cur);
      // do not letify id 0
      if (itl != letMap.end() && itl->second > 0)
      {
        // make the let variable
        std::stringstream ss;
        ss << prefix << itl->second;
        visited[cur] = nm->mkBoundVar(ss.str(), cur.getType());
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

void Letify::computeLet(Node n,
                        std::vector<Node>& letList,
                        std::map<Node, uint32_t>& letMap,
                        uint32_t thresh)
{
  Assert(letList.empty() && letMap.empty());
  if (thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  std::vector<Node> visitList;
  std::map<Node, uint32_t> count;
  updateCounts(n, visitList, count);
  // Now populate the letList and letMap
  convertCountToLet(visitList, count, letList, letMap, thresh);
}

void Letify::updateCounts(Node n,
                          std::vector<Node>& visitList,
                          std::map<Node, uint32_t>& count)
{
  std::map<Node, uint32_t>::iterator it;
  std::vector<Node> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    it = count.find(cur);
    if (it == count.end())
    {
      if (cur.getNumChildren() == 0 || cur.isClosure())
      {
        visitList.push_back(cur);
        count[cur] = 1;
      }
      else
      {
        count[cur] = 0;
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else
    {
      if (it->second == 0)
      {
        visitList.push_back(cur);
      }
      count[cur]++;
      visit.pop_back();
    }
  } while (!visit.empty());
}

void Letify::updateCounts(const ProofNode* pn,
                          std::vector<Node>& visitList,
                          std::map<Node, uint32_t>& count)
{
  // TODO?
}

void Letify::convertCountToLet(const std::vector<Node>& visitList,
                               const std::map<Node, uint32_t>& count,
                               std::vector<Node>& letList,
                               std::map<Node, uint32_t>& letMap,
                               uint32_t thresh)
{
  Assert(letList.empty() && letMap.empty());
  if (thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<Node, uint32_t>::const_iterator itc;
  for (const Node& n : visitList)
  {
    if (n.getNumChildren() == 0)
    {
      // do not letify terms with no children
      continue;
    }
    itc = count.find(n);
    Assert(itc != count.end());
    if (itc->second >= thresh)
    {
      letList.push_back(n);
      // start with id 1
      size_t id = letMap.size() + 1;
      letMap[n] = id;
    }
  }
}

void Letify::computeProofLet(const ProofNode* pn,
                             std::vector<const ProofNode*>& pletList,
                             std::map<const ProofNode*, uint32_t>& pletMap,
                             uint32_t thresh)
{
  Assert(pletList.empty() && pletMap.empty());
  if (thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  std::vector<const ProofNode*> visitList;
  std::map<const ProofNode*, uint32_t> pcount;
  computeProofCounts(pn, visitList, pcount);
  // Now populate the pletList and pletMap
  convertProofCountToLet(visitList, pcount, pletList, pletMap, thresh);
}

void Letify::computeProofCounts(const ProofNode* pn,
                                std::vector<const ProofNode*>& visitList,
                                std::map<const ProofNode*, uint32_t>& pcount)
{
  std::map<const ProofNode*, uint32_t>::iterator it;
  std::vector<const ProofNode*> visit;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    it = pcount.find(cur);
    if (it == pcount.end())
    {
      pcount[cur] = 0;
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        visit.push_back(cp.get());
      }
    }
    else
    {
      if (it->second == 0)
      {
        visitList.push_back(cur);
      }
      pcount[cur]++;
      visit.pop_back();
    }
  } while (!visit.empty());
}

void Letify::convertProofCountToLet(
    const std::vector<const ProofNode*>& visitList,
    const std::map<const ProofNode*, uint32_t>& pcount,
    std::vector<const ProofNode*>& pletList,
    std::map<const ProofNode*, uint32_t>& pletMap,
    uint32_t thresh)
{
  Assert(pletList.empty() && pletMap.empty());
  if (thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<const ProofNode*, uint32_t>::const_iterator itc;
  for (const ProofNode* pn : visitList)
  {
    itc = pcount.find(pn);
    Assert(itc != pcount.end());
    if (itc->second >= thresh)
    {
      pletList.push_back(pn);
      // start with id 1
      size_t id = pletMap.size() + 1;
      pletMap[pn] = id;
    }
  }
}

}  // namespace proof
}  // namespace CVC4
