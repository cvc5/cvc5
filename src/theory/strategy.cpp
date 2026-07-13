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
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {

StrategyBase::StrategyBase(TheoryId id,
                           TheoryState* state,
                           InferenceManagerBuffered* im,
                           Valuation* valuation)
    : d_theoryId(id),
      d_state(state),
      d_im(im),
      d_valuation(valuation),
      d_strategyInit(false)
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
  std::map<Theory::Effort, std::pair<unsigned, unsigned>>::const_iterator it =
      d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_steps.begin() + it->second.first;
}

std::vector<std::pair<Step, Theory::Effort>>::iterator StrategyBase::stepEnd(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<unsigned, unsigned>>::const_iterator it =
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
  for (const std::pair<const Theory::Effort, unsigned>& b : d_stepBegin)
  {
    Theory::Effort e = b.first;
    std::map<Theory::Effort, unsigned>::const_iterator itEnd =
        d_stepEnd.find(e);
    Assert(itEnd != d_stepEnd.end());
    d_stratSteps[e] = std::pair<unsigned, unsigned>(b.second, itEnd->second);
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

void StrategyBase::postCheck(Theory::Effort e)
{
  d_im->doPendingFacts();

  Assert(isStrategyInit());
  if (!d_state->isInConflict() && !d_valuation->needCheck()
      && hasStrategyEffort(e))
  {
    Trace("check-debug") << "Theory of " << d_theoryId << " " << e
                         << " effort check " << std::endl;

    // ToDo: ++(d_statistics->d_checkRuns);
    bool sentLemma = false;
    bool hadPending = false;
    do
    {
      d_im->reset();
      // ++(d_statistics->d_strategyRuns);
      Trace("check") << "  * Run strategy..." << std::endl;
      runStrategy(e);
      // Remember if this round produced work. Conclusions may be buffered as
      // pending facts/lemmas (hasPending), or facts may be asserted immediately
      // to the equality engine, which only shows up via hasSentFact. Either
      // case means the round was productive and we should iterate again (unless
      // we end up sending a lemma or hitting a conflict below).
      hadPending = d_im->hasPending() || d_im->hasSentFact();
      // Send the facts *and* the lemmas. We send lemmas regardless of whether
      // we send facts since some lemmas cannot be dropped. Other lemmas are
      // otherwise avoided by aborting the strategy when a fact is ready.
      d_im->doPending();
      // Did we successfully send a lemma? Notice that if hasPending = true
      // and sentLemma = false, then the above call may have:
      // (1) had no pending lemmas, but successfully processed pending facts,
      // (2) unsuccessfully processed pending lemmas.
      // In either case, we repeat the strategy if we are not in conflict.
      sentLemma = d_im->hasSentLemma();
      if (TraceIsOn("check"))
      {
        Trace("check") << "  ...finish run strategy: ";
        Trace("check") << (hadPending ? "hadPending " : "");
        Trace("check") << (sentLemma ? "sentLemma " : "");
        Trace("check") << (d_state->isInConflict() ? "conflict " : "");
        if (!hadPending && !sentLemma && !d_state->isInConflict())
        {
          Trace("check") << "(none)";
        }
        Trace("check") << std::endl;
      }
      // repeat if we did not add a lemma or conflict, and we had pending
      // facts or lemmas.
    } while (!d_state->isInConflict() && !sentLemma && hadPending);
  }
  Trace("check") << "Theory of " << d_theoryId << ", done check : " << e
                 << std::endl;
  Assert(!d_im->hasPendingFact());
  Assert(!d_im->hasPendingLemma());
}

}  // namespace theory
}  // namespace cvc5::internal
