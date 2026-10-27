/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the strategy of the theory of bags.
 */

#include "theory/bags/strategy.h"

#include "theory/bags/bag_solver.h"
#include "theory/bags/theory_bags.h"
#include "theory/inference_manager_buffered.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

Strategy::Strategy(TheoryBags* parent,
                   BagSolver* solver,
                   TheoryState* state,
                   InferenceManagerBuffered* im)
    : StrategyBase(TheoryId::THEORY_BAGS, state, im),
      d_theory(parent),
      d_bagSolver(solver)
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
  // add the inference steps
  addStrategyStep(Step::BAGS_CHECK_INIT);
  addStrategyStep(Step::BAGS_CHECK_BAG_MAKE);
  addStrategyStep(Step::BAGS_CHECK_BASIC_OPERATIONS);
  addStrategyStep(Step::BAGS_CHECK_QUANTIFIED_OPERATIONS);
  markEndEffort(Theory::EFFORT_FULL);
  // set the beginning/ending ranges and mark the strategy as initialized
  finishInit();
}

void Strategy::runStep(Step s, Theory::Effort, Theory::Effort effort)
{
  Trace("bags-process") << "Run " << s << ", effort = " << effort << "..."
                        << std::endl;
  Assert(d_theory != nullptr && d_bagSolver != nullptr);
  switch (s)
  {
    case Step::BAGS_CHECK_INIT: d_theory->initialize(); break;
    case Step::BAGS_CHECK_BAG_MAKE: d_bagSolver->checkBagMake(); break;
    case Step::BAGS_CHECK_BASIC_OPERATIONS:
      d_bagSolver->checkBasicOperations();
      break;
    case Step::BAGS_CHECK_QUANTIFIED_OPERATIONS:
      d_bagSolver->checkQuantifiedOperations();
      break;
    default: Unreachable(); break;
  }
  Trace("bags-process") << "Done " << s
                        << ", addedFact = " << d_im->hasPendingFact()
                        << ", addedLemma = " << d_im->hasPendingLemma()
                        << ", conflict = " << d_state->isInConflict()
                        << std::endl;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
