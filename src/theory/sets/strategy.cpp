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
                   InferenceManagerBuffered* im,
                   Valuation* valuation)
    : StrategyBase(TheoryId::THEORY_SETS, state, im, valuation),
      d_setsSolver(parent)
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
  addStrategyStep(SETS_CHECK_RESET);
  addStrategyStep(SETS_CHECK_BASIC);
  addStrategyStep(SETS_CHECK_RELATIONS);
  addStrategyStep(SETS_CHECK_ACYCLICITY);
  addStrategyStep(SETS_CHECK_TRANSITIVE_CLOSURE);
  addStrategyStep(SETS_CHECK_FILTER);
  addStrategyStep(SETS_CHECK_MAP);
  addStrategyStep(SETS_CHECK_GROUP);
  addStrategyStep(SETS_CHECK_DISEQUALITY);
  addStrategyStep(SETS_CHECK_CARDINALITY);
  addStrategyStep(SETS_CHECK_COMPREHENSION);
  markEndEffort(Theory::EFFORT_FULL);
  // set the beginning/ending ranges and mark the strategy as initialized
  finishInit();
}

void Strategy::runStep(Step s, Theory::Effort, unsigned effort)
{
  Trace("sets-process") << "Run " << s;
  if (effort > 0)
  {
    Trace("sets-process") << ", effort = " << effort;
  }
  Trace("sets-process") << "..." << std::endl;
  Assert(d_setsSolver != nullptr);
  switch (s)
  {
    case Step::SETS_CHECK_RESET: d_setsSolver->fullEffortReset(); break;
    case Step::SETS_CHECK_BASIC: d_setsSolver->checkBasic(); break;
    case Step::SETS_CHECK_CARDINALITY: d_setsSolver->checkCardinality(); break;
    case Step::SETS_CHECK_RELATIONS: d_setsSolver->checkRelations(); break;
    case Step::SETS_CHECK_ACYCLICITY: d_setsSolver->checkAcyclicity(); break;
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
