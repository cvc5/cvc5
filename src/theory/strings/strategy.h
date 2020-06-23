/*********************                                                        */
/*! \file strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strategy of the theory of strings
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__STRATEGY_H
#define CVC4__THEORY__STRINGS__STRATEGY_H

#include <map>
#include <vector>

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** inference steps
 *
 * Corresponds to a step in the overall strategy of the strings solver. For
 * details on the individual steps, see documentation on the inference schemas
 * within Strategy.
 */
enum InferStep
{
  // indicates that the strategy should break if lemmas or facts are added
  BREAK,
  // check initial
  CHECK_INIT,
  // check constant equivalence classes
  CHECK_CONST_EQC,
  // check extended function evaluation
  CHECK_EXTF_EVAL,
  // check cycles
  CHECK_CYCLES,
  // check flat forms
  CHECK_FLAT_FORMS,
  // check register terms pre-normal forms
  CHECK_REGISTER_TERMS_PRE_NF,
  // check normal forms equalities
  CHECK_NORMAL_FORMS_EQ,
  // check normal forms disequalities
  CHECK_NORMAL_FORMS_DEQ,
  // check codes
  CHECK_CODES,
  // check lengths for equivalence classes
  CHECK_LENGTH_EQC,
  // check register terms for normal forms
  CHECK_REGISTER_TERMS_NF,
  // check extended function reductions
  CHECK_EXTF_REDUCTION,
  // check regular expression memberships
  CHECK_MEMBERSHIP,
  // check cardinality
  CHECK_CARDINALITY,
};
std::ostream& operator<<(std::ostream& out, InferStep i);

/**
 * The strategy of theory of strings.
 *
 * This stores a sequence of the above enum that indicates the calls to
 * runInferStep to make on the theory of strings, given by parent.
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
  std::vector<std::pair<InferStep, int> >::iterator stepBegin(Theory::Effort e);
  std::vector<std::pair<InferStep, int> >::iterator stepEnd(Theory::Effort e);
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
  std::vector<std::pair<InferStep, int> > d_infer_steps;
  /** the range (begin, end) of steps to run at given efforts */
  std::map<Theory::Effort, std::pair<unsigned, unsigned> > d_strat_steps;
}; /* class Strategy */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRATEGY_H */
