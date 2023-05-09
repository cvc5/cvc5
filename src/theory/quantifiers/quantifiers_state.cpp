/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for quantifiers state.
 */

#include "theory/quantifiers/quantifiers_state.h"

#include "options/quantifiers_options.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/equality_engine_iterator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersState::QuantifiersState(Env& env,
                                   Valuation val,
                                   const LogicInfo& logicInfo)
    : TheoryState(env, val),
      d_ierCounterc(env.getContext()),
      d_logicInfo(logicInfo),
      d_statistics(statisticsRegistry())
{
  // allow theory combination to go first, once initially
  d_ierCounter = 0;
  d_ierCounterc = d_ierCounter;
  d_ierCounterLc = 0;
  d_ierCounterLastLc = 0;
  d_instWhenPhase = 1
                    + (options().quantifiers.instWhenPhase < 1
                           ? 1
                           : options().quantifiers.instWhenPhase);
}

void QuantifiersState::incrementInstRoundCounters(Theory::Effort e)
{
  if (e == Theory::EFFORT_FULL)
  {
    // increment if a last call happened, or already were in phase
    if (d_ierCounterLastLc != d_ierCounterLc
        || d_ierCounter % d_instWhenPhase != 0)
    {
      d_ierCounter = d_ierCounter + 1;
      d_ierCounterLastLc = d_ierCounterLc;
      d_ierCounterc = d_ierCounterc.get() + 1;
    }
  }
  else if (e == Theory::EFFORT_LAST_CALL)
  {
    d_ierCounterLc = d_ierCounterLc + 1;
  }
}

bool QuantifiersState::getInstWhenNeedsCheck(Theory::Effort e) const
{
  Trace("qstate-debug") << "Get inst when needs check, counts=" << d_ierCounter
                        << ", " << d_ierCounterLc << std::endl;
  // determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if (options().quantifiers.instWhenMode == options::InstWhenMode::FULL)
  {
    performCheck = (e >= Theory::EFFORT_FULL);
  }
  else if (options().quantifiers.instWhenMode
           == options::InstWhenMode::FULL_DELAY)
  {
    performCheck = (e >= Theory::EFFORT_FULL) && !d_valuation.needCheck();
  }
  else if (options().quantifiers.instWhenMode
           == options::InstWhenMode::FULL_LAST_CALL)
  {
    performCheck =
        ((e == Theory::EFFORT_FULL && d_ierCounter % d_instWhenPhase != 0)
         || e == Theory::EFFORT_LAST_CALL);
  }
  else if (options().quantifiers.instWhenMode
           == options::InstWhenMode::FULL_DELAY_LAST_CALL)
  {
    performCheck = ((e == Theory::EFFORT_FULL && !d_valuation.needCheck()
                     && d_ierCounter % d_instWhenPhase != 0)
                    || e == Theory::EFFORT_LAST_CALL);
  }
  else if (options().quantifiers.instWhenMode
           == options::InstWhenMode::LAST_CALL)
  {
    performCheck = (e >= Theory::EFFORT_LAST_CALL);
  }
  else
  {
    performCheck = true;
  }
  Trace("qstate-debug") << "...returned " << performCheck << std::endl;
  return performCheck;
}

uint64_t QuantifiersState::getInstRoundDepth() const
{
  return d_ierCounterc.get();
}

uint64_t QuantifiersState::getInstRounds() const { return d_ierCounter; }

void QuantifiersState::debugPrintEqualityEngine(const char* c) const
{
  bool traceEnabled = TraceIsOn(c);
  if (!traceEnabled)
  {
    return;
  }
  eq::EqualityEngine* ee = getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  std::map<TypeNode, uint64_t> tnum;
  while (!eqcs_i.isFinished())
  {
    tnum[(*eqcs_i).getType()]++;
    ++eqcs_i;
  }
  Trace(c) << ee->debugPrintEqc() << std::endl;
  for (const std::pair<const TypeNode, uint64_t>& t : tnum)
  {
    Trace(c) << "# eqc for " << t.first << " : " << t.second << std::endl;
  }
}

const LogicInfo& QuantifiersState::getLogicInfo() const { return d_logicInfo; }

QuantifiersStatistics& QuantifiersState::getStats() { return d_statistics; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
