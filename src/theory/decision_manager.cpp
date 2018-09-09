/*********************                                                        */
/*! \file decision_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of decision_manager
 **/

#include "theory/decision_manager.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

DecisionManager::DecisionManager(context::Context* satContext)
{
}

void DecisionManager::reset()
{
  Trace("dec-manager") << "DecisionManager: reset." << std::endl;
  d_reg_strategy.clear();
}

void DecisionManager::registerStrategy(StrategyId id,
                                       DecisionStrategy* ds,
                                       bool append)
{
  ds->initialize();
  Trace("dec-manager") << "DecisionManager: Register strategy : "
                       << ds->identify() << ", id = " << id << std::endl;
  if (append)
  {
    d_reg_strategy[id].push_back(ds);
  }
  else
  {
    std::vector<DecisionStrategy*>& stid = d_reg_strategy[id];
    stid.insert(stid.begin(), ds);
  }
}

Node DecisionManager::getNextDecisionRequest(unsigned& priority)
{
  Trace("dec-manager-debug")
      << "DecisionManager: Get next decision..." << std::endl;
  for (const std::pair<StrategyId, std::vector<DecisionStrategy*> >& rs :
       d_reg_strategy)
  {
    for (unsigned i = 0, size = rs.second.size(); i < size; i++)
    {
      DecisionStrategy* ds = rs.second[i];
      Node lit = ds->getNextDecisionRequest();
      if (!lit.isNull())
      {
        StrategyId sid = rs.first;
        priority = sid < strat_last_m_sound
                       ? 0
                       : (sid < strat_last_fm_complete ? 1 : 2);
        Trace("dec-manager")
            << "DecisionManager:  -> literal " << lit << " decided by strategy "
            << ds->identify() << std::endl;
        return lit;
      }
      else
      {
        Trace("dec-manager-debug") << "DecisionManager:  " << ds->identify()
                                   << " has no decisions." << std::endl;
      }
    }
  }
  Trace("dec-manager-debug")
      << "DecisionManager:  -> no decisions." << std::endl;
  return Node::null();
}

}  // namespace theory
}  // namespace CVC4
