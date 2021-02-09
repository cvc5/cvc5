/*********************                                                        */
/*! \file quantifiers_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for quantifiers state
 **/

#include "theory/quantifiers/quantifiers_state.h"

#include "options/quantifiers_options.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

QuantifiersState::QuantifiersState(context::Context* c,
                                   context::UserContext* u,
                                   Valuation val)
    : TheoryState(c, u, val), d_ierCounterc(c)
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

bool QuantifiersState::getInstWhenNeedsCheck(Theory::Effort e)
{
  Trace("quant-engine-debug2")
      << "Get inst when needs check, counts=" << d_ierCounter << ", "
      << d_ierCounterLc << std::endl;
  // determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if (options::instWhenMode() == options::InstWhenMode::FULL)
  {
    performCheck = (e >= Theory::EFFORT_FULL);
  }
  else if (options::instWhenMode() == options::InstWhenMode::FULL_DELAY)
  {
    performCheck =
        (e >= Theory::EFFORT_FULL) && !d_qstate.getValuation().needCheck();
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
    performCheck =
        ((e == Theory::EFFORT_FULL && !d_qstate.getValuation().needCheck()
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
  return performCheck;
}

options::UserPatMode QuantifiersState::getInstUserPatMode()
{
  if (options::userPatternsQuant() == options::UserPatMode::INTERLEAVE)
  {
    return d_ierCounter % 2 == 0 ? options::UserPatMode::USE
                                 : options::UserPatMode::RESORT;
  }
  return options::userPatternsQuant();
}

int64_t getInstRoundDepth() const
{
  return d_ierCounterc.get();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
