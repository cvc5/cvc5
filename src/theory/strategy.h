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

#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

/**
 * Generic base class for a theory "strategy".
 *
 * A strategy is an ordered list of inference steps that a theory runs during
 * its full-effort (and, optionally, last-call) check. Several theories (e.g.
 * strings and bags) historically reimplemented byte-for-byte identical
 * bookkeeping for:
 *   - storing the ordered list of steps,
 *   - inserting BREAK markers between steps,
 *   - recording, per Theory::Effort, the index range of the list to run.
 *
 * This template factors out that shared bookkeeping so that a new theory can
 * add a strategy with only a few lines of theory-specific code. A theory
 * specializes it by:
 *   1. defining its own `enum [class] Step` of inference steps, which MUST
 *      contain a dedicated BREAK marker;
 *   2. deriving `class Strategy : public StrategyBase<Step> { ... }`;
 *   3. implementing initializeStrategy() to build the list using the protected
 *      helpers below (markStartEffort / addStrategyStep / markEndEffort /
 *      finishInit);
 *   4. adding an explicit instantiation `template class StrategyBase<Step>;` to
 *      strategy.cpp (the template member definitions live there, not here).
 *
 * The theory's own check loop (typically runStrategy / runInferStep) is
 * intentionally NOT part of this class: those dispatch to theory-specific
 * sub-solvers and may apply theory-specific BREAK semantics. This class owns
 * only the *recipe* (the ordered list and its per-effort slices); the theory
 * owns how the recipe is executed.
 *
 * The step list is stored flat. For an effort e, the steps to run are the
 * half-open iterator range [stepBegin(e), stepEnd(e)). Note that stepEnd(e)
 * points at the trailing BREAK of the last step for e (i.e. the list index
 * size()-1 at the time markEndEffort(e) was called), so that final BREAK is
 * excluded from iteration. This matches the long-standing behavior of the
 * per-theory implementations this class replaces.
 *
 * @tparam Step The theory's inference-step enum type. It must be equality
 *              comparable and copyable. Both plain `enum` and `enum class`
 *              work.
 */
template <typename Step>
class StrategyBase
{
 public:
  /**
   * @param breakStep The value of `Step` that denotes a BREAK marker. A BREAK
   * is inserted automatically after each step added with addBreak=true; the
   * theory's runStrategy treats a BREAK as a yield point.
   */
  StrategyBase(Step breakStep);
  virtual ~StrategyBase();

  /** Has initializeStrategy() finished building the strategy? */
  bool isStrategyInit() const;

  /** Is there a sequence of steps registered for effort e? */
  bool hasStrategyEffort(Theory::Effort e) const;

  /** Begin iterator over the steps to run at effort e. */
  typename std::vector<std::pair<Step, int> >::iterator stepBegin(
      Theory::Effort e);

  /** End iterator over the steps to run at effort e. */
  typename std::vector<std::pair<Step, int> >::iterator stepEnd(
      Theory::Effort e);

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
  /** The designated BREAK marker for this theory's Step type. */
  const Step d_break;
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

class InferenceManagerBuffered;
class TheoryState;

/**
 * Callback interface implemented by a theory that is driven by
 * postCheckStrategy(). It exposes the small set of theory-specific operations
 * the shared full-effort check loop needs: the strategy queries, a single pass
 * over the strategy steps, flushing buffered facts/lemmas, and optional hooks
 * run at the boundaries of the check. A theory typically implements this
 * interface on the Theory subclass itself and forwards to its members.
 */
class StrategyCallback
{
 public:
  virtual ~StrategyCallback() = default;
  /** Has the strategy been initialized? (typically d_strat.isStrategyInit()) */
  virtual bool isStrategyInit() const = 0;
  /** Is there a strategy for effort e? (typically d_strat.hasStrategyEffort(e))
   */
  virtual bool hasStrategyEffort(Theory::Effort e) const = 0;
  /** Run one pass over the strategy steps at effort e. */
  virtual void runStrategy(Theory::Effort e) = 0;
  /**
   * Send all buffered facts and then lemmas (typically d_im.doPending()). This
   * is routed through the callback because each theory's inference manager
   * defines its own doPending().
   */
  virtual void doPending() = 0;
  /** Optional hook: called once before the first strategy round. */
  virtual void notifyStrategyCheckStart(Theory::Effort) {}
  /**
   * Optional hook: called each round, after the inference manager is reset and
   * before runStrategy().
   */
  virtual void notifyStrategyRoundStart(Theory::Effort) {}
  /** Optional hook: called once after the last strategy round. */
  virtual void notifyStrategyCheckEnd(Theory::Effort) {}
};

/**
 * The shared full-effort "strategy check" driver, factored out of the
 * per-theory postCheck implementations.
 *
 * It runs the standard loop: flush pending facts, then (if not in conflict, a
 * check is needed, and a strategy exists for effort e) repeatedly run the
 * strategy and flush its output, stopping as soon as a lemma is sent or a
 * conflict is reached, and otherwise continuing while a round produced internal
 * facts only. A theory uses it by implementing StrategyCallback and calling
 * this from its Theory::postCheck.
 *
 * @param e The effort of the check.
 * @param cb The theory's callback (typically the theory itself).
 * @param im The theory's (buffered) inference manager.
 * @param state The theory's state, used to detect conflicts.
 * @param valuation The theory's valuation, used to detect whether a check is
 *                  needed.
 */
void postCheckStrategy(Theory::Effort e,
                       StrategyCallback& cb,
                       InferenceManagerBuffered& im,
                       TheoryState& state,
                       Valuation& valuation);

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRATEGY_H */
