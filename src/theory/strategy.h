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
#include <string>
#include <utility>
#include <vector>

#include "theory/step.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

class InferenceManagerBuffered;

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
 * The theory's own check loop (typically runStrategy / runStep) is
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
  StrategyBase(TheoryId id,
               TheoryState* state = nullptr,
               InferenceManagerBuffered* im = nullptr,
               Valuation* valuation = nullptr);

  /** a destructor */
  virtual ~StrategyBase();

  /** Has initializeStrategy() finished building the strategy? */
  bool isStrategyInit() const;

  /** Is there a sequence of steps registered for effort e? */
  bool hasStrategyEffort(Theory::Effort e) const;

  /** Begin iterator over the steps to run at effort e. */
  std::vector<std::pair<Step, unsigned>>::iterator stepBegin(Theory::Effort e);

  /** End iterator over the steps to run at effort e. */
  std::vector<std::pair<Step, unsigned>>::iterator stepEnd(Theory::Effort e);

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

  /**
   * The standard full/last-call effort check loop.
   * It repeatedly runs the strategy and sends pending
   * facts/lemmas until a conflict or lemma is produced or nothing is pending.
   */
  virtual void postCheck(Theory::Effort e);

  /**ToDo: move this to InferenceManagerBuffered with new field TheoryState */
  void doPending();

 protected:
  /**
   * Run the steps registered for effort e in order, dispatching each via
   * runStep() and yielding at BREAK markers once something has been
   * processed or a conflict is found.
   */
  void runStrategy(Theory::Effort e);

  /**
   * Execute a single inference step.
   */
  virtual void runStep(Step s, Theory::Effort e, unsigned effort) = 0;

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

  bool hasProcessed() const;

 private:
  TheoryId d_theoryId;
  TheoryState* d_state;
  InferenceManagerBuffered* d_im;
  Valuation* d_valuation;
  /** Whether the strategy has been initialized. */
  bool d_strategyInit;
  /** The flat ordered list of steps, with BREAK markers interleaved. */
  std::vector<std::pair<Step, unsigned>> d_steps;
  /** For each effort, the [begin,end] index range into d_inferSteps. */
  std::map<Theory::Effort, std::pair<unsigned, unsigned>> d_stratSteps;
  /** Scratch: per-effort begin indices recorded by markStartEffort. */
  std::map<Theory::Effort, unsigned> d_stepBegin;
  /** Scratch: per-effort end indices recorded by markEndEffort. */
  std::map<Theory::Effort, unsigned> d_stepEnd;
}; /* class StrategyBase */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRATEGY_H */
