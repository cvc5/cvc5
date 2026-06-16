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
// The headers below define the Step enum types that StrategyBase is explicitly
// instantiated with at the bottom of this file. A new theory that adds a
// strategy must include its Step enum here and add a matching explicit
// instantiation.
#include "theory/bags/strategy.h"
#include "theory/strings/strategy.h"

namespace cvc5::internal {
namespace theory {

template <typename Step>
StrategyBase<Step>::StrategyBase(Step breakStep)
    : d_break(breakStep), d_strategyInit(false)
{
}

template <typename Step>
StrategyBase<Step>::~StrategyBase()
{
}

template <typename Step>
bool StrategyBase<Step>::isStrategyInit() const
{
  return d_strategyInit;
}

template <typename Step>
bool StrategyBase<Step>::hasStrategyEffort(Theory::Effort e) const
{
  return d_stratSteps.find(e) != d_stratSteps.end();
}

template <typename Step>
typename std::vector<std::pair<Step, int> >::iterator
StrategyBase<Step>::stepBegin(Theory::Effort e)
{
  typename std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator
      it = d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_inferSteps.begin() + it->second.first;
}

template <typename Step>
typename std::vector<std::pair<Step, int> >::iterator
StrategyBase<Step>::stepEnd(Theory::Effort e)
{
  typename std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator
      it = d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_inferSteps.begin() + it->second.second;
}

template <typename Step>
void StrategyBase<Step>::addStrategyStep(Step s, int effort, bool addBreak)
{
  // BREAK markers are inserted automatically and must never be added by hand.
  Assert(s != d_break);
  d_inferSteps.push_back(std::pair<Step, int>(s, effort));
  if (addBreak)
  {
    d_inferSteps.push_back(std::pair<Step, int>(d_break, 0));
  }
}

template <typename Step>
void StrategyBase<Step>::markStartEffort(Theory::Effort e)
{
  d_stepBegin[e] = d_inferSteps.size();
}

template <typename Step>
void StrategyBase<Step>::markEndEffort(Theory::Effort e)
{
  // markStartEffort(e) must have been called before markEndEffort(e), and at
  // least one step must have been added for effort e. This is the generic
  // well-formedness check that replaces the old per-theory assertion that the
  // first step added was that theory's CHECK_INIT step.
  Assert(d_stepBegin.find(e) != d_stepBegin.end());
  Assert(d_inferSteps.size() > d_stepBegin.find(e)->second);
  d_stepEnd[e] = d_inferSteps.size() - 1;
}

template <typename Step>
void StrategyBase<Step>::finishInit()
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

// Explicit instantiations for the theories that use the strategy framework.
// Because the template member definitions live in this .cpp, every theory that
// derives from StrategyBase<Step> must add its instantiation here.
template class StrategyBase<strings::InferStep>;
template class StrategyBase<bags::InferStep>;

}  // namespace theory
}  // namespace cvc5::internal
