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
#include "base/output.h"
#include "theory/inference_manager_buffered.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {

StrategyBase::StrategyBase(TheoryId id,
                           TheoryState* state,
                           InferenceManagerBuffered* im)
    : d_theoryId(id), d_state(state), d_im(im), d_strategyInit(false)
{
}

StrategyBase::~StrategyBase() {}

bool StrategyBase::isStrategyInit() const { return d_strategyInit; }

bool StrategyBase::hasStrategyEffort(Theory::Effort e) const
{
  return d_stratSteps.find(e) != d_stratSteps.end();
}

std::vector<std::pair<Step, Theory::Effort>>::iterator StrategyBase::stepBegin(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<size_t, size_t>>::const_iterator it =
      d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_steps.begin() + it->second.first;
}

std::vector<std::pair<Step, Theory::Effort>>::iterator StrategyBase::stepEnd(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<size_t, size_t>>::const_iterator it =
      d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_steps.begin() + it->second.second;
}

void StrategyBase::addStrategyStep(Step s, Theory::Effort effort, bool addBreak)
{
  Assert(s != BREAK);
  d_steps.push_back(std::pair<Step, Theory::Effort>(s, effort));
  if (addBreak)
  {
    d_steps.push_back(std::pair<Step, Theory::Effort>(BREAK, effort));
  }
}

void StrategyBase::markStartEffort(Theory::Effort e)
{
  d_stepBegin[e] = d_steps.size();
}

void StrategyBase::markEndEffort(Theory::Effort e)
{
  // markStartEffort(e) must have been called before markEndEffort(e), and at
  // least one step must have been added for effort e.
  Assert(d_stepBegin.find(e) != d_stepBegin.end());
  Assert(d_steps.size() > d_stepBegin.find(e)->second);
  d_stepEnd[e] = d_steps.size() - 1;
}

void StrategyBase::finishInit()
{
  for (const std::pair<const Theory::Effort, size_t>& b : d_stepBegin)
  {
    Theory::Effort e = b.first;
    std::map<Theory::Effort, size_t>::const_iterator itEnd = d_stepEnd.find(e);
    Assert(itEnd != d_stepEnd.end());
    d_stratSteps[e] = std::pair<size_t, size_t>(b.second, itEnd->second);
  }
  // the begin/end marks are scratch state only needed while building the
  // strategy; drop them so no stale data persists after initialization.
  d_stepBegin.clear();
  d_stepEnd.clear();
  d_strategyInit = true;
}

void StrategyBase::runStrategy(Theory::Effort e)
{
  std::vector<std::pair<Step, Theory::Effort>>::iterator it = stepBegin(e);
  std::vector<std::pair<Step, Theory::Effort>>::iterator end = stepEnd(e);

  Trace("strings-process") << "----check, next round---" << std::endl;
  while (it != end)
  {
    Step curr = it->first;
    Theory::Effort effort = it->second;
    if (curr == Step::BREAK)
    {
      // if we have a pending inference or lemma, we will process it
      if (d_im->hasProcessed())
      {
        break;
      }
    }
    else
    {
      runStep(curr, e, effort);
      if (d_state->isInConflict())
      {
        break;
      }
    }
    ++it;
  }
  Trace("strings-process") << "----finished round---" << std::endl;
}

}  // namespace theory
}  // namespace cvc5::internal
