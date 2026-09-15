/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Strategy of the theory of sets.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__STRATEGY_H
#define CVC5__THEORY__SETS__STRATEGY_H

#include "theory/strategy.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

class TheorySetsPrivate;

/**
 * The strategy of theory of sets.
 * This class supplies the sets-specific step ordering in initializeStrategy()
 * and dispatches each step (via runStep) to the corresponding check method on
 * the owning TheorySetsPrivate.
 */
class Strategy : public StrategyBase
{
 public:
  Strategy(TheorySetsPrivate* parent = nullptr,
           TheoryState* state = nullptr,
           InferenceManagerBuffered* im = nullptr);

  ~Strategy();
  /** initialize the strategy
   *
   * This makes a series of calls to addStrategyStep (inherited from
   * StrategyBase) to build the sets strategy.
   */
  void initializeStrategy() override;

  /**
   * Execute a single inference step by dispatching to the matching check
   * method on the owning TheorySetsPrivate.
   */
  void runStep(Step s, Theory::Effort e, Theory::Effort effort) override;

 private:
  /** The sets solver that owns this strategy and implements the steps. */
  TheorySetsPrivate* d_setsSolver;
}; /* class Strategy */

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__STRATEGY_H */
