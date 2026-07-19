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

#include "theory/inference_manager_buffered.h"
#include "theory/sets/theory_sets_private.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

Strategy::Strategy(TheorySetsPrivate* parent,
                   TheoryState* state,
                   InferenceManagerBuffered* im)
    : StrategyBase(TheoryId::THEORY_SETS, state, im), d_setsSolver(parent)
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
  addStrategyStep(Step::SETS_CHECK_RESET);
  addStrategyStep(Step::SETS_CHECK_BASIC);
  addStrategyStep(Step::SETS_CHECK_RELATIONS);
  addStrategyStep(Step::SETS_CHECK_TRANSITIVE_CLOSURE);
  addStrategyStep(Step::SETS_CHECK_FILTER);
  addStrategyStep(Step::SETS_CHECK_MAP);
  addStrategyStep(Step::SETS_CHECK_GROUP);
  addStrategyStep(Step::SETS_CHECK_DISEQUALITY);
  addStrategyStep(Step::SETS_CHECK_CARDINALITY);
  addStrategyStep(Step::SETS_CHECK_COMPREHENSION);
  markEndEffort(Theory::EFFORT_FULL);
  // set the beginning/ending ranges and mark the strategy as initialized
  finishInit();
}

void Strategy::runStep(Step s, Theory::Effort, Theory::Effort effort)
{
  Trace("sets-process") << "Run " << s << ", effort = " << effort << "..."
                        << std::endl;
  Assert(d_setsSolver != nullptr);
  switch (s)
  {
    case Step::SETS_CHECK_RESET: d_setsSolver->fullEffortReset(); break;
    case Step::SETS_CHECK_BASIC: d_setsSolver->checkBasic(); break;
    case Step::SETS_CHECK_CARDINALITY: d_setsSolver->checkCardinality(); break;
    case Step::SETS_CHECK_RELATIONS: d_setsSolver->checkRelations(); break;
    case Step::SETS_CHECK_TRANSITIVE_CLOSURE:
      d_setsSolver->checkTransitiveClosure();
      break;
    case Step::SETS_CHECK_FILTER: d_setsSolver->checkFilters(); break;
    case Step::SETS_CHECK_MAP: d_setsSolver->checkMaps(); break;
    case Step::SETS_CHECK_GROUP: d_setsSolver->checkGroups(); break;
    case Step::SETS_CHECK_DISEQUALITY:
      d_setsSolver->checkDisequalities();
      break;
    case Step::SETS_CHECK_COMPREHENSION:
      d_setsSolver->checkReduceComprehensions();
      break;

    default: Unreachable(); break;
  }
  // Sets asserts facts directly to the equality engine, so "addedFact" is
  // reported via hasSentFact rather than the pending-fact queue.
  Trace("sets-process") << "Done " << s
                        << ", addedFact = " << d_im->hasSentFact()
                        << ", addedLemma = " << d_im->hasPendingLemma()
                        << ", conflict = " << d_state->isInConflict()
                        << std::endl;
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
