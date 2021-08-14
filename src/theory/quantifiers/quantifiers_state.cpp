/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for quantifiers state.
 */

#include "theory/quantifiers/quantifiers_state.h"

#include "options/quantifiers_options.h"
#include "theory/uf/equality_engine_iterator.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

QuantifiersState::QuantifiersState(Env& env,
                                   Valuation val,
                                   const LogicInfo& logicInfo)
    : TheoryState(env, val),
      d_ierCounterc(env.getContext()),
      d_logicInfo(logicInfo)
{
  // allow theory combination to go first, once initially
  d_ierCounter = options::instWhenTcFirst() ? 0 : 1;
  d_ierCounterc = d_ierCounter;
  d_ierCounterLc = 0;
  d_ierCounterLastLc = 0;
  d_instWhenPhase =
      1 + (options::instWhenPhase() < 1 ? 1 : options::instWhenPhase());
}

void QuantifiersState::incrementInstRoundCounters(Theory::Effort e)
{
  if (e == Theory::EFFORT_FULL)
  {
    // increment if a last call happened, we are not strictly enforcing
    // interleaving, or already were in phase
    if (d_ierCounterLastLc != d_ierCounterLc
        || !options::instWhenStrictInterleave()
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
  if (options::instWhenMode() == options::InstWhenMode::FULL)
  {
    performCheck = (e >= Theory::EFFORT_FULL);
  }
  else if (options::instWhenMode() == options::InstWhenMode::FULL_DELAY)
  {
    performCheck = (e >= Theory::EFFORT_FULL) && !d_valuation.needCheck();
  }
  else if (options::instWhenMode() == options::InstWhenMode::FULL_LAST_CALL)
  {
    performCheck =
        ((e == Theory::EFFORT_FULL && d_ierCounter % d_instWhenPhase != 0)
         || e == Theory::EFFORT_LAST_CALL);
  }
  else if (options::instWhenMode()
           == options::InstWhenMode::FULL_DELAY_LAST_CALL)
  {
    performCheck = ((e == Theory::EFFORT_FULL && !d_valuation.needCheck()
                     && d_ierCounter % d_instWhenPhase != 0)
                    || e == Theory::EFFORT_LAST_CALL);
  }
  else if (options::instWhenMode() == options::InstWhenMode::LAST_CALL)
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
  bool traceEnabled = Trace.isOn(c);
  if (!traceEnabled)
  {
    return;
  }
  eq::EqualityEngine* ee = getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(ee);
  std::map<TypeNode, uint64_t> tnum;
  while (!eqcs_i.isFinished())
  {
    TNode r = (*eqcs_i);
    TypeNode tr = r.getType();
    if (tnum.find(tr) == tnum.end())
    {
      tnum[tr] = 0;
    }
    tnum[tr]++;
    bool firstTime = true;
    Trace(c) << "  " << r;
    Trace(c) << " : { ";
    eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
    while (!eqc_i.isFinished())
    {
      TNode n = (*eqc_i);
      if (r != n)
      {
        if (firstTime)
        {
          Trace(c) << std::endl;
          firstTime = false;
        }
        Trace(c) << "    " << n << std::endl;
      }
      ++eqc_i;
    }
    if (!firstTime)
    {
      Trace(c) << "  ";
    }
    Trace(c) << "}" << std::endl;
    ++eqcs_i;
  }
  Trace(c) << std::endl;
  for (const std::pair<const TypeNode, uint64_t>& t : tnum)
  {
    Trace(c) << "# eqc for " << t.first << " : " << t.second << std::endl;
  }
}

const LogicInfo& QuantifiersState::getLogicInfo() const { return d_logicInfo; }

QuantifiersStatistics& QuantifiersState::getStats() { return d_statistics; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
