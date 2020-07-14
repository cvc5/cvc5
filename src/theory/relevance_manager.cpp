/*********************                                                        */
/*! \file relevance_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of relevance manager
 **/

#include "theory/relevance_manager.h"

namespace CVC4 {
namespace theory {

RelevanceManager::RelevanceManager(context::UserContext* userContext, Valuation val) : d_input(userContext), d_val(val), d_success(false){}

void RelevanceManager::notifyPreprocessedAssertions(const std::vector<Node>& assertions)
{
  // add to input list, which is user-context dependent
  for (const Node& a : assertions)
  {
    d_input.insert(a);
  }
}

void RelevanceManager::computeRelevance()
{
  std::unordered_map<TNode, int, TNodeHashFunction> cache;
  for (NodeList::const_iterator it = d_input.begin(); it != d_input.end(); ++it)
  {
    TNode n = *it;
    if (!justify(n, cache))
    {
      d_success = false;
      return;
    }
  }
  d_success = true;
}

bool RelevanceManager::justify(TNode n, std::unordered_map<TNode, int, TNodeHashFunction>& cache)
{
  std::unordered_map<TNode, int, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end()) {
      visited[cur] = false;
      /** TODO pre-visit */
      
      visit.push_back(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push_back(cur[i]);
      }
    }else if( !it->second ){
      /** TODO post-visit */      
      visited[cur] = true;
    }
  } while (!visit.empty());
  return false;
}

bool RelevanceManager::isRelevant(Node lit) const
{
  if (!d_success)
  {
    return true;
  }
  return d_rset.find(lit)!=d_rset.end();
}

}  // namespace theory
}  // namespace CVC4

