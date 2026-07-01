/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

#include "theory/strategy.h"
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
  // check basic operations without quantifiers
  CHECK_BASIC_OPERATIONS,
  // check operations with quantifiers
  CHECK_QUANTIFIED_OPERATIONS
};
std::ostream& operator<<(std::ostream& out, InferStep i);

/**
 * The strategy of theory of bags.
 *
 * This stores a sequence of the above enum that indicates the calls to
 * runInferStep to make on the theory of bags, given by parent. All of the
 * generic bookkeeping (storing the ordered list, inserting BREAK markers and
 * recording per-effort ranges) is inherited from theory::StrategyBase; this
 * class only supplies the bags-specific step ordering in initializeStrategy().
 */
class Strategy : public StrategyBase<InferStep>
{
 public:
  Strategy();
  ~Strategy();
  /** initialize the strategy
   *
   * This makes a series of calls to addStrategyStep (inherited from
   * StrategyBase) to build the bags strategy.
   */
  void initializeStrategy() override;
}; /* class Strategy */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__STRATEGY_H */
