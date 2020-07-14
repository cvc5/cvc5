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

RelevanceManager::RelevanceManager(context::UserContext* userContext, Valuation& val) : d_input(userContext), d_val(val){}

void RelevanceManager::notifyPreprocessedAssertions(const std::vector<Node>& assertions)
{
  // add to input
  for (const Node& a : assertions)
  {
    d_input.insert(a);
  }
}

void RelevanceManager::computeRelevance()
{
  
}

bool RelevanceManager::isRelevant(Node lit)
{
  return true;
}

}  // namespace theory
}  // namespace CVC4

