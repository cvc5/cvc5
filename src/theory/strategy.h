/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A generic, reusable strategy container shared by theory solvers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRATEGY_H
#define CVC5__THEORY__STRATEGY_H

#include <map>
#include <utility>
#include <vector>

#include "theory/step.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

/**
 * Generic base class for a theory "strategy".
 *
 * A strategy is an ordered list of inference steps that a theory runs during
 * its standard, full or last-call effort check.
 *
 * A new theory can add a strategy with only a few lines of theory-specific
 * code. A theory specializes it by:
 *   1. adding enum `Step` with its own inference steps.
 *   2. deriving `class Strategy : public StrategyBase { ... }`;
 *   3. implementing initializeStrategy() to build the list using the protected
 *      helpers below (markStartEffort / addStrategyStep / markEndEffort /
 *      finishInit).
 * The theory's own check loop (typically runStrategy / runInferStep) is
 * intentionally NOT part of this class: those dispatch to theory-specific
 * sub-solvers.
 * This class owns only the *recipe* (the ordered list and its per-effort
 * slices); the theory owns how the recipe is executed.
 *
 * The step list is stored flat. For an effort e, the steps to run are the
 * half-open iterator range [stepBegin(e), stepEnd(e)).
 *
 */
class StrategyBase
{
 public:
  /** a destructor */
  virtual ~StrategyBase() = 0;

  /** Has initializeStrategy() finished building the strategy? */
  bool isStrategyInit() const;

  /** Is there a sequence of steps registered for effort e? */
  bool hasStrategyEffort(Theory::Effort e) const;

  /** Begin iterator over the steps to run at effort e. */
  std::vector<std::pair<Step, int> >::iterator stepBegin(Theory::Effort e);

  /** End iterator over the steps to run at effort e. */
  std::vector<std::pair<Step, int> >::iterator stepEnd(Theory::Effort e);

  /**
   * Build the strategy. Implemented by each theory's derived class. A typical
   * implementation looks like:
   *
   *   if (isStrategyInit()) return;
   *   markStartEffort(Theory::EFFORT_FULL);
   *   addStrategyStep(MY_FIRST_STEP);
   *   ...
   *   addStrategyStep(MY_LAST_STEP);
   *   markEndEffort(Theory::EFFORT_FULL);
   *   finishInit();
   *
   * Multiple efforts (e.g. EFFORT_LAST_CALL) can be registered by issuing
   * additional markStartEffort/.../markEndEffort blocks before finishInit().
   */
  virtual void initializeStrategy() = 0;

 protected:
  /**
   * Append step s (running at the given effort index) to the strategy. If
   * addBreak is true (default), a BREAK marker is appended after it, which the
   * theory's runStrategy uses as a yield point.
   */
  void addStrategyStep(Step s, int effort = 0, bool addBreak = true);

  /**
   * Mark that the steps for effort e begin at the current end of the list.
   * Call this immediately before adding the steps for effort e.
   */
  void markStartEffort(Theory::Effort e);

  /**
   * Mark that the steps for effort e end at the current end of the list. Call
   * this immediately after adding the steps for effort e. The recorded end
   * index is the trailing BREAK of the last step (size()-1), which is excluded
   * from iteration; see the class-level note on stepEnd().
   */
  void markEndEffort(Theory::Effort e);

  /**
   * Finalize the strategy: compute the per-effort index ranges from the marks
   * recorded above and flag the strategy as initialized. Must be called once,
   * after all steps and effort marks have been added.
   */
  void finishInit();

 private:
  /** Whether the strategy has been initialized. */
  bool d_strategyInit;
  /** The flat ordered list of steps, with BREAK markers interleaved. */
  std::vector<std::pair<Step, int> > d_inferSteps;
  /** For each effort, the [begin,end] index range into d_inferSteps. */
  std::map<Theory::Effort, std::pair<size_t, size_t> > d_stratSteps;
  /** Scratch: per-effort begin indices recorded by markStartEffort. */
  std::map<Theory::Effort, size_t> d_stepBegin;
  /** Scratch: per-effort end indices recorded by markEndEffort. */
  std::map<Theory::Effort, size_t> d_stepEnd;
}; /* class StrategyBase */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRATEGY_H */
