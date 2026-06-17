/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the generic, reusable strategy container.
 */

#include "theory/strategy.h"

#include "base/check.h"

namespace cvc5::internal {
namespace theory {

StrategyBase::~StrategyBase() {}

bool StrategyBase::isStrategyInit() const { return d_strategyInit; }

bool StrategyBase::hasStrategyEffort(Theory::Effort e) const
{
  return d_stratSteps.find(e) != d_stratSteps.end();
}

typename std::vector<std::pair<Step, int> >::iterator StrategyBase::stepBegin(
    Theory::Effort e)
{
  typename std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator
      it = d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_inferSteps.begin() + it->second.first;
}

typename std::vector<std::pair<Step, int> >::iterator StrategyBase::stepEnd(
    Theory::Effort e)
{
  typename std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator
      it = d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_inferSteps.begin() + it->second.second;
}

void StrategyBase::addStrategyStep(Step s, int effort, bool addBreak)
{
  // BREAK markers are inserted automatically and must never be added by hand.
  Assert(s != BREAK);
  d_inferSteps.push_back(std::pair<Step, int>(s, effort));
  if (addBreak)
  {
    d_inferSteps.push_back(std::pair<Step, int>(BREAK, 0));
  }
}

void StrategyBase::markStartEffort(Theory::Effort e)
{
  d_stepBegin[e] = d_inferSteps.size();
}

void StrategyBase::markEndEffort(Theory::Effort e)
{
  // markStartEffort(e) must have been called before markEndEffort(e), and at
  // least one step must have been added for effort e.
  Assert(d_stepBegin.find(e) != d_stepBegin.end());
  Assert(d_inferSteps.size() > d_stepBegin.find(e)->second);
  d_stepEnd[e] = d_inferSteps.size() - 1;
}

void StrategyBase::finishInit()
{
  for (const std::pair<const Theory::Effort, size_t>& b : d_stepBegin)
  {
    Theory::Effort e = b.first;
    typename std::map<Theory::Effort, size_t>::const_iterator itEnd =
        d_stepEnd.find(e);
    Assert(itEnd != d_stepEnd.end());
    d_stratSteps[e] = std::pair<size_t, size_t>(b.second, itEnd->second);
  }
  // the begin/end marks are scratch state only needed while building the
  // strategy; drop them so no stale data persists after initialization.
  d_stepBegin.clear();
  d_stepEnd.clear();
  d_strategyInit = true;
}

}  // namespace theory
}  // namespace cvc5::internal
