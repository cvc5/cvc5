/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for computing letification of proofs.
 */

#include "proof/proof_letify.h"

namespace cvc5::internal {
namespace proof {

bool ProofLetifyTraverseCallback::shouldTraverse(const ProofNode* pn)
{
  return pn->getRule() != PfRule::SCOPE;
}

void ProofLetify::computeProofLet(const ProofNode* pn,
                                  std::vector<const ProofNode*>& pletList,
                                  std::map<const ProofNode*, size_t>& pletMap,
                                  size_t thresh,
                                  ProofLetifyTraverseCallback* pltc)
{
  Assert(pletList.empty() && pletMap.empty());
  if (thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  std::vector<const ProofNode*> visitList;
  std::map<const ProofNode*, size_t> pcount;
  if (pltc == nullptr)
  {
    // use default callback
    ProofLetifyTraverseCallback defaultPltc;
    computeProofCounts(pn, visitList, pcount, &defaultPltc);
  }
  else
  {
    computeProofCounts(pn, visitList, pcount, pltc);
  }
  // Now populate the pletList and pletMap
  convertProofCountToLet(visitList, pcount, pletList, pletMap, thresh);
}

void ProofLetify::computeProofCounts(const ProofNode* pn,
                                     std::vector<const ProofNode*>& visitList,
                                     std::map<const ProofNode*, size_t>& pcount,
                                     ProofLetifyTraverseCallback* pltc)
{
  std::map<const ProofNode*, size_t>::iterator it;
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
      if (!pltc->shouldTraverse(cur))
      {
        // callback indicated we should not traverse
        continue;
      }
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

void ProofLetify::convertProofCountToLet(
    const std::vector<const ProofNode*>& visitList,
    const std::map<const ProofNode*, size_t>& pcount,
    std::vector<const ProofNode*>& pletList,
    std::map<const ProofNode*, size_t>& pletMap,
    size_t thresh)
{
  Assert(pletList.empty() && pletMap.empty());
  if (thresh == 0)
  {
    // value of 0 means do not introduce let
    return;
  }
  // Assign ids for those whose count is > 1, traverse in reverse order
  // so that deeper proofs are assigned lower identifiers
  std::map<const ProofNode*, size_t>::const_iterator itc;
  for (const ProofNode* pn : visitList)
  {
    itc = pcount.find(pn);
    Assert(itc != pcount.end());
    if (itc->second >= thresh && pn->getRule() != PfRule::ASSUME)
    {
      pletList.push_back(pn);
      // start with id 1
      size_t id = pletMap.size() + 1;
      pletMap[pn] = id;
    }
  }
}

}  // namespace proof
}  // namespace cvc5::internal
