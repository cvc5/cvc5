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
 * Strategy of the theory of bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__STRATEGY_H
#define CVC5__THEORY__BAGS__STRATEGY_H

#include <map>
#include <vector>

#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

/** inference steps
 *
 * Corresponds to a step in the overall strategy of the bags solver. For
 * details on the individual steps, see documentation on the inference schemas
 * within Strategy.
 */
enum InferStep
{
  // indicates that the strategy should break if lemmas or facts are added
  BREAK,
  // check initial
  CHECK_INIT,
  // check bag operator
  CHECK_BAG_MAKE,
  // check basic operations
  CHECK_BASIC_OPERATIONS,
  // check cardinality constraints
  CHECK_CARDINALITY_CONSTRAINTS
};
std::ostream& operator<<(std::ostream& out, InferStep i);

/**
 * The strategy of theory of bags.
 *
 * This stores a sequence of the above enum that indicates the calls to
 * runInferStep to make on the theory of bags, given by parent.
 */
class Strategy
{
 public:
  Strategy();
  ~Strategy();
  /** is this strategy initialized? */
  bool isStrategyInit() const;
  /** do we have a strategy for effort e? */
  bool hasStrategyEffort(Theory::Effort e) const;
  /** begin and end iterators for effort e */
  std::vector<std::pair<InferStep, size_t> >::iterator stepBegin(
      Theory::Effort e);
  std::vector<std::pair<InferStep, size_t> >::iterator stepEnd(
      Theory::Effort e);
  /** initialize the strategy
   *
   * This initializes the above information based on the options. This makes
   * a series of calls to addStrategyStep above.
   */
  void initializeStrategy();

 private:
  /** add strategy step
   *
   * This adds (s,effort) as a strategy step to the vectors d_infer_steps and
   * d_infer_step_effort. This indicates that a call to runInferStep should
   * be run as the next step in the strategy. If addBreak is true, we add
   * a BREAK to the strategy following this step.
   */
  void addStrategyStep(InferStep s, int effort = 0, bool addBreak = true);
  /** is strategy initialized */
  bool d_strategy_init;
  /** the strategy */
  std::vector<std::pair<InferStep, size_t> > d_infer_steps;
  /** the range (begin, end) of steps to run at given efforts */
  std::map<Theory::Effort, std::pair<size_t, size_t> > d_strat_steps;
}; /* class Strategy */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__STRATEGY_H */
