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

#include "base/check.h"
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
 *      finishInit).
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
  StrategyBase(Step breakStep) : d_break(breakStep), d_strategyInit(false) {}
  virtual ~StrategyBase() {}

  /** Has initializeStrategy() finished building the strategy? */
  bool isStrategyInit() const { return d_strategyInit; }

  /** Is there a sequence of steps registered for effort e? */
  bool hasStrategyEffort(Theory::Effort e) const
  {
    return d_stratSteps.find(e) != d_stratSteps.end();
  }

  /** Begin iterator over the steps to run at effort e. */
  typename std::vector<std::pair<Step, int> >::iterator stepBegin(
      Theory::Effort e)
  {
    typename std::map<Theory::Effort,
                      std::pair<size_t, size_t> >::const_iterator it =
        d_stratSteps.find(e);
    Assert(it != d_stratSteps.end());
    return d_inferSteps.begin() + it->second.first;
  }

  /** End iterator over the steps to run at effort e. */
  typename std::vector<std::pair<Step, int> >::iterator stepEnd(
      Theory::Effort e)
  {
    typename std::map<Theory::Effort,
                      std::pair<size_t, size_t> >::const_iterator it =
        d_stratSteps.find(e);
    Assert(it != d_stratSteps.end());
    return d_inferSteps.begin() + it->second.second;
  }

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
  void addStrategyStep(Step s, int effort = 0, bool addBreak = true)
  {
    // BREAK markers are inserted automatically and must never be added by hand.
    Assert(s != d_break);
    d_inferSteps.push_back(std::pair<Step, int>(s, effort));
    if (addBreak)
    {
      d_inferSteps.push_back(std::pair<Step, int>(d_break, 0));
    }
  }

  /**
   * Mark that the steps for effort e begin at the current end of the list.
   * Call this immediately before adding the steps for effort e.
   */
  void markStartEffort(Theory::Effort e)
  {
    d_stepBegin[e] = d_inferSteps.size();
  }

  /**
   * Mark that the steps for effort e end at the current end of the list. Call
   * this immediately after adding the steps for effort e. The recorded end
   * index is the trailing BREAK of the last step (size()-1), which is excluded
   * from iteration; see the class-level note on stepEnd().
   */
  void markEndEffort(Theory::Effort e)
  {
    // markStartEffort(e) must have been called before markEndEffort(e), and at
    // least one step must have been added for effort e. This is the generic
    // well-formedness check that replaces the old per-theory assertion that the
    // first step added was that theory's CHECK_INIT step.
    Assert(d_stepBegin.find(e) != d_stepBegin.end());
    Assert(d_inferSteps.size() > d_stepBegin.find(e)->second);
    d_stepEnd[e] = d_inferSteps.size() - 1;
  }

  /**
   * Finalize the strategy: compute the per-effort index ranges from the marks
   * recorded above and flag the strategy as initialized. Must be called once,
   * after all steps and effort marks have been added.
   */
  void finishInit()
  {
    for (const std::pair<const Theory::Effort, size_t>& b : d_stepBegin)
    {
      Theory::Effort e = b.first;
      typename std::map<Theory::Effort, size_t>::const_iterator itEnd =
          d_stepEnd.find(e);
      Assert(itEnd != d_stepEnd.end());
      d_stratSteps[e] = std::pair<size_t, size_t>(b.second, itEnd->second);
    }
    // the begin/end marks are scratch state only needed while building the
    // strategy; drop them so no stale data persists after initialization.
    d_stepBegin.clear();
    d_stepEnd.clear();
    d_strategyInit = true;
  }

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

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRATEGY_H */
