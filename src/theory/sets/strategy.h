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

/**
 * The strategy of theory of sets.
 * This class only supplies the sets-specific step ordering in
 * initializeStrategy().
 */
class Strategy : public StrategyBase
{
 public:
  Strategy();
  ~Strategy();
  /** initialize the strategy
   *
   * This makes a series of calls to addStrategyStep (inherited from
   * StrategyBase) to build the sets strategy.
   */
  void initializeStrategy() override;
}; /* class Strategy */

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SETS__STRATEGY_H */
