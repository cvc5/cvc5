/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
    case CHECK_CARDINALITY_CONSTRAINTS:
      out << "CHECK_CARDINALITY_CONSTRAINTS";
      break;
    default: out << "?"; break;
  }
  return out;
}

Strategy::Strategy() : d_strategy_init(false) {}

Strategy::~Strategy() {}

bool Strategy::isStrategyInit() const { return d_strategy_init; }

bool Strategy::hasStrategyEffort(Theory::Effort e) const
{
  return d_strat_steps.find(e) != d_strat_steps.end();
}

std::vector<std::pair<InferStep, size_t> >::iterator Strategy::stepBegin(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator it =
      d_strat_steps.find(e);
  Assert(it != d_strat_steps.end());
  return d_infer_steps.begin() + it->second.first;
}

std::vector<std::pair<InferStep, size_t> >::iterator Strategy::stepEnd(
    Theory::Effort e)
{
  std::map<Theory::Effort, std::pair<size_t, size_t> >::const_iterator it =
      d_strat_steps.find(e);
  Assert(it != d_strat_steps.end());
  return d_infer_steps.begin() + it->second.second;
}

void Strategy::addStrategyStep(InferStep s, int effort, bool addBreak)
{
  // must run check init first
  Assert((s == CHECK_INIT) == d_infer_steps.empty());
  d_infer_steps.push_back(std::pair<InferStep, int>(s, effort));
  if (addBreak)
  {
    d_infer_steps.push_back(std::pair<InferStep, int>(BREAK, 0));
  }
}

void Strategy::initializeStrategy()
{
  // initialize the strategy if not already done so
  if (!d_strategy_init)
  {
    std::map<Theory::Effort, unsigned> step_begin;
    std::map<Theory::Effort, unsigned> step_end;
    d_strategy_init = true;
    // beginning indices
    step_begin[Theory::EFFORT_FULL] = 0;
    // add the inference steps
    addStrategyStep(CHECK_INIT);
    addStrategyStep(CHECK_BAG_MAKE);
    addStrategyStep(CHECK_BASIC_OPERATIONS);
    addStrategyStep(CHECK_CARDINALITY_CONSTRAINTS);
    step_end[Theory::EFFORT_FULL] = d_infer_steps.size() - 1;

    // set the beginning/ending ranges
    for (const std::pair<const Theory::Effort, unsigned>& it_begin : step_begin)
    {
      Theory::Effort e = it_begin.first;
      std::map<Theory::Effort, unsigned>::iterator it_end = step_end.find(e);
      Assert(it_end != step_end.end());
      d_strat_steps[e] =
          std::pair<unsigned, unsigned>(it_begin.second, it_end->second);
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
