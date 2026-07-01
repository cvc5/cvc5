/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Strategy of the theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__STRATEGY_H
#define CVC5__THEORY__STRINGS__STRATEGY_H

#include <map>
#include <vector>

#include "theory/strategy.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/** inference steps
 *
 * Corresponds to a step in the overall strategy of the strings solver. For
 * details on the individual steps, see documentation on the inference schemas
 * within Strategy.
 */
enum class InferStep : uint32_t
{
  // placeholder specfying no inference step
  NONE,

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
  // check normal forms equalities, propagate only
  CHECK_NORMAL_FORMS_EQ_PROP,
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
  // check for eager extended function reductions
  CHECK_EXTF_REDUCTION_EAGER,
  // check extended function reductions
  CHECK_EXTF_REDUCTION,
  // check regular expression memberships eagerly (prior to CAV 14 procedure)
  CHECK_MEMBERSHIP_EAGER,
  // check regular expression memberships
  CHECK_MEMBERSHIP,
  // check cardinality
  CHECK_CARDINALITY,
  // check sequence updates wrt concat
  CHECK_SEQUENCES_ARRAY_CONCAT,
  // check sequence array-like reasoning
  CHECK_SEQUENCES_ARRAY,
  // check sequence
  CHECK_SEQUENCES_ARRAY_EAGER,

  // unknown inference step
  UNKNOWN
};
std::ostream& operator<<(std::ostream& out, InferStep i);

/**
 * The strategy of theory of strings.
 *
 * This stores a sequence of the above enum that indicates the calls to
 * runInferStep to make on the theory of strings, given by parent. All of the
 * generic bookkeeping (storing the ordered list, inserting BREAK markers and
 * recording per-effort ranges) is inherited from theory::StrategyBase; this
 * class only supplies the strings-specific step ordering in
 * initializeStrategy().
 */
class Strategy : public StrategyBase<InferStep>, protected EnvObj
{
 public:
  Strategy(Env& env);
  ~Strategy();
  /** initialize the strategy
   *
   * This initializes the strategy based on the options. This makes a series of
   * calls to addStrategyStep (inherited from StrategyBase).
   */
  void initializeStrategy() override;
}; /* class Strategy */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__STRATEGY_H */
