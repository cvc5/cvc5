/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Decision manager, which manages all decision
 * strategies owned by theory solvers within TheoryEngine.
 */

#include "theory/decision_manager.h"

#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

DecisionManager::DecisionManager(context::Context* userContext)
    : d_strategyCacheC(userContext)
{
}

void DecisionManager::presolve()
{
  Trace("dec-manager") << "DecisionManager: presolve." << std::endl;
  // remove the strategies that are not in this user context
  std::unordered_set<DecisionStrategy*> active;
  for (DecisionStrategyList::const_iterator i = d_strategyCacheC.begin();
       i != d_strategyCacheC.end();
       ++i)
  {
    active.insert(*i);
  }
  active.insert(d_strategyCache.begin(), d_strategyCache.end());
  std::map<StrategyId, std::vector<DecisionStrategy*> > tmp = d_reg_strategy;
  d_reg_strategy.clear();
  for (std::pair<const StrategyId, std::vector<DecisionStrategy*> >& rs : tmp)
  {
    for (DecisionStrategy* ds : rs.second)
    {
      if (active.find(ds) != active.end())
      {
        // if its active, we keep it
        d_reg_strategy[rs.first].push_back(ds);
      }
    }
  }
}

void DecisionManager::registerStrategy(StrategyId id,
                                       DecisionStrategy* ds,
                                       StrategyScope sscope)
{
  Trace("dec-manager") << "DecisionManager: Register strategy : "
                       << ds->identify() << ", id = " << id << std::endl;
  ds->initialize();
  d_reg_strategy[id].push_back(ds);
  if (sscope == STRAT_SCOPE_USER_CTX_DEPENDENT)
  {
    // store it in the user-context-dependent list
    d_strategyCacheC.push_back(ds);
  }
  else if (sscope == STRAT_SCOPE_CTX_INDEPENDENT)
  {
    // it is context independent
    d_strategyCache.insert(ds);
  }
  else
  {
    // it is local to this call, we don't cache it
    Assert(sscope == STRAT_SCOPE_LOCAL_SOLVE);
  }
}

Node DecisionManager::getNextDecisionRequest()
{
  Trace("dec-manager-debug")
      << "DecisionManager: Get next decision..." << std::endl;
  for (const std::pair<const StrategyId, std::vector<DecisionStrategy*> >& rs :
       d_reg_strategy)
  {
    for (unsigned i = 0, size = rs.second.size(); i < size; i++)
    {
      DecisionStrategy* ds = rs.second[i];
      Node lit = ds->getNextDecisionRequest();
      if (!lit.isNull())
      {
        Trace("dec-manager")
            << "DecisionManager:  -> literal " << lit << " decided by strategy "
            << ds->identify() << std::endl;
        return lit;
      }
      Trace("dec-manager-debug") << "DecisionManager:  " << ds->identify()
                                 << " has no decisions." << std::endl;
    }
  }
  Trace("dec-manager-debug")
      << "DecisionManager:  -> no decisions." << std::endl;
  return Node::null();
}

}  // namespace theory
}  // namespace cvc5::internal
