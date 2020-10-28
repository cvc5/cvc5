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

void Letify::computeLet(Node n,
                             std::vector<Node>& letList,
                             std::map<Node, uint32_t>& letMap,
                             uint32_t& counter)
{
  Assert(letList.empty() && letMap.empty());
  std::vector<Node> visitList;
  std::map<Node, uint32_t> count;
  updateCounts(n, visitList, count);
  // Now populate the letList and letMap
  convertCountToLet(visitList, count, letList, letMap, counter);
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
      count[cur] = 0;
      visitList.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else
    {
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
                                    uint32_t& counter)
{
  Assert(letList.empty() && letMap.empty());
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<Node, uint32_t>::const_iterator itc;
  for (std::vector<Node>::const_reverse_iterator it = visitList.rbegin();
       it != visitList.rend();
       ++it)
  {
    itc = count.find(*it);
    Assert(itc != count.end());
    if (itc->second > 1)
    {
      letList.push_back(*it);
      letMap[*it] = counter;
      counter++;
    }
  }
}

void Letify::computeProofLet(const ProofNode* pn,
                                  std::vector<const ProofNode*>& pletList,
                                  std::map<const ProofNode*, uint32_t>& pletMap,
                                  uint32_t& pcounter)
{
  Assert(pletList.empty() && pletMap.empty());
  std::vector<const ProofNode*> visitList;
  std::map<const ProofNode*, uint32_t> pcount;
  computeProofCounts(pn, visitList, pcount);
  // Now populate the pletList and pletMap
  convertProofCountToLet(visitList, pcount, pletList, pletMap, pcounter);
}

void Letify::computeProofCounts(
    const ProofNode* pn,
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
      visitList.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        visit.push_back(cp.get());
      }
    }
    else
    {
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
    uint32_t& pcounter)
{
  Assert(pletList.empty() && pletMap.empty());
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<const ProofNode*, uint32_t>::const_iterator itc;
  for (std::vector<const ProofNode*>::const_reverse_iterator itp =
           visitList.rbegin();
       itp != visitList.rend();
       ++itp)
  {
    itc = pcount.find(*itp);
    Assert(itc != pcount.end());
    if (itc->second > 1)
    {
      pletList.push_back(*itp);
      pletMap[*itp] = pcounter;
      pcounter++;
    }
  }
}


}  // namespace proof
}  // namespace CVC4
