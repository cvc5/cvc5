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

#include "theory/strategy.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class BagSolver;
class TheoryBags;

/**
 * The strategy of theory of bags.
 */
class Strategy : public StrategyBase
{
 public:
  Strategy(TheoryBags* parent = nullptr,
           BagSolver* solver = nullptr,
           TheoryState* state = nullptr,
           InferenceManagerBuffered* im = nullptr);

  ~Strategy();
  /** initialize the strategy
   *
   * This makes a series of calls to addStrategyStep (inherited from
   * StrategyBase) to build the bags strategy.
   */
  void initializeStrategy() override;

  /**
   * Execute a single inference step by dispatching to the matching check
   * method on the owning TheoryBags or on its bag solver.
   */
  void runStep(Step s, Theory::Effort e, Theory::Effort effort) override;

 private:
  /** The theory of bags that owns this strategy. */
  TheoryBags* d_theory;
  /** The bag solver that implements most of the steps. */
  BagSolver* d_bagSolver;
}; /* class Strategy */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__STRATEGY_H */
