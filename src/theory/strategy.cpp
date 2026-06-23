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

std::vector<std::pair<Step, int> >::iterator StrategyBase::stepBegin(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator it =
      d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_inferSteps.begin() + it->second.first;
}

std::vector<std::pair<Step, int> >::iterator StrategyBase::stepEnd(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator it =
      d_stratSteps.find(e);
  Assert(it != d_stratSteps.end());
  return d_inferSteps.begin() + it->second.second;
}

void StrategyBase::addStrategyStep(Step s, int effort, bool addBreak)
{
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

void StrategyBase::runStrategy(Theory::Effort) {}

void StrategyBase::doPending()
{
  d_im->doPendingFacts();
  if (d_state->isInConflict())
  {
    // just clear the pending vectors, nothing else to do
    d_im->clearPendingLemmas();
    d_im->clearPendingPhaseRequirements();
    return;
  }
  d_im->doPendingLemmas();
  d_im->doPendingPhaseRequirements();
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
      Trace("strings-check") << "  * Run strategy..." << std::endl;
      runStrategy(e);
      // remember if we had pending facts or lemmas
      hadPending = d_im->hasPending();
      // Send the facts *and* the lemmas. We send lemmas regardless of whether
      // we send facts since some lemmas cannot be dropped. Other lemmas are
      // otherwise avoided by aborting the strategy when a fact is ready.
      doPending();
      // Did we successfully send a lemma? Notice that if hasPending = true
      // and sentLemma = false, then the above call may have:
      // (1) had no pending lemmas, but successfully processed pending facts,
      // (2) unsuccessfully processed pending lemmas.
      // In either case, we repeat the strategy if we are not in conflict.
      sentLemma = d_im->hasSentLemma();
      if (TraceIsOn("strings-check"))
      {
        Trace("strings-check") << "  ...finish run strategy: ";
        Trace("strings-check") << (hadPending ? "hadPending " : "");
        Trace("strings-check") << (sentLemma ? "sentLemma " : "");
        Trace("strings-check") << (d_state->isInConflict() ? "conflict " : "");
        if (!hadPending && !sentLemma && !d_state->isInConflict())
        {
          Trace("strings-check") << "(none)";
        }
        Trace("strings-check") << std::endl;
      }
      // repeat if we did not add a lemma or conflict, and we had pending
      // facts or lemmas.
    } while (!d_state->isInConflict() && !sentLemma && hadPending);
  }
  Trace("strings-check") << "Theory of strings, done check : " << e
                         << std::endl;
  Assert(!d_im->hasPendingFact());
  Assert(!d_im->hasPendingLemma());
}

}  // namespace theory
}  // namespace cvc5::internal
