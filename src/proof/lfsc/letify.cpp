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
