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

#include <iosfwd>

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STEP_H
#define CVC5__THEORY__STEP_H

namespace cvc5::internal {
namespace theory {

/** inference steps
 *
 * Corresponds to a step in the overall strategy of a theory solver.
 * This enums contains steps for all theory solvers that implement a
 * strategy.
 */
enum Step : uint32_t
{
  // placeholder specfying no inference step
  NONE,

  // indicates that the strategy should break if lemmas or facts are added
  BREAK,
  // reset the per-pass full-effort state
  SETS_CHECK_RESET,
  // check basic sets operations
  SETS_CHECK_BASIC,
  // check cardinality operations
  SETS_CHECK_CARDINALITY,
  // check basic relational operators
  SETS_CHECK_RELATIONS,
  // check acyclicity
  SETS_CHECK_ACYCLICITY,
  // check transitive closure
  SETS_CHECK_TRANSITIVE_CLOSURE,
  // check filter
  SETS_CHECK_FILTER,
  // check map
  SETS_CHECK_MAP,
  // check group
  SETS_CHECK_GROUP,
  // check disequalities
  SETS_CHECK_DISEQUALITY,
  // check comprehension reductions
  SETS_CHECK_COMPREHENSION,
  // unknown inference step
  UNKNOWN
};
std::ostream& operator<<(std::ostream& out, Step i);

}  // namespace theory
}  // namespace cvc5::internal
#endif /* CVC5__THEORY__STEP_H */