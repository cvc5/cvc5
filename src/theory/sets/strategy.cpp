/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the strategy of the theory of sets.
 */

#include "theory/sets/strategy.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

Strategy::Strategy(TheoryState* state,
                   InferenceManagerBuffered* im,
                   Valuation* valuation)
    : StrategyBase(TheoryId::THEORY_SETS, state, im, valuation)
{
}

Strategy::~Strategy() {}

void Strategy::initializeStrategy()
{
  // initialize the strategy if not already done so
  if (isStrategyInit())
  {
    return;
  }
  // the full-effort strategy
  markStartEffort(Theory::EFFORT_FULL);
  // add the ence steps
  addStrategyStep(SETS_CHECK_BASIC);
  addStrategyStep(SETS_CHECK_CARDINALITY);
  addStrategyStep(SETS_CHECK_RELATIONS);
  addStrategyStep(SETS_CHECK_TRANSITIVE_CLOSURE);
  addStrategyStep(SETS_CHECK_FOLD);
  markEndEffort(Theory::EFFORT_FULL);
  // set the beginning/ending ranges and mark the strategy as initialized
  finishInit();
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
