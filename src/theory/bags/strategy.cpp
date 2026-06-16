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

namespace cvc5::internal {
namespace theory {
namespace bags {

std::ostream& operator<<(std::ostream& out, InferStep s)
{
  switch (s)
  {
    case BREAK: out << "break"; break;
    case CHECK_INIT: out << "check_init"; break;
    case CHECK_BAG_MAKE: out << "check_bag_make"; break;
    case CHECK_BASIC_OPERATIONS: out << "CHECK_BASIC_OPERATIONS"; break;
    default: out << "?"; break;
  }
  return out;
}

Strategy::Strategy() : StrategyBase<InferStep>(BREAK) {}

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
  addStrategyStep(CHECK_INIT);
  addStrategyStep(CHECK_BAG_MAKE);
  addStrategyStep(CHECK_BASIC_OPERATIONS);
  addStrategyStep(CHECK_QUANTIFIED_OPERATIONS);
  markEndEffort(Theory::EFFORT_FULL);
  // set the beginning/ending ranges and mark the strategy as initialized
  finishInit();
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
