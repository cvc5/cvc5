/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Incompleteness enumeration.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__INCOMPLETE_ID_H
#define CVC5__THEORY__INCOMPLETE_ID_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {

/**
 * Reasons for answering "unknown" in cvc5.
 *
 * Note that this enumeration is used both for marking incomplete in a
 * SAT context, and marking unsound in a user context, both of which may
 * imply that we are "unknown".
 */
enum class IncompleteId
{
  // the non-linear arithmetic solver was disabled
  ARITH_NL_DISABLED,
  // the non-linear arithmetic solver was incomplete
  ARITH_NL,
  // incomplete due to lack of a complete quantifiers strategy
  QUANTIFIERS,
  // (refutation unsound) we failed to verify the correctness of a candidate
  // solution in SyGuS and blocked it to make progress
  QUANTIFIERS_SYGUS_NO_VERIFY,
  // (refutation unsound) we are generalizing any-constants when blocking with
  // smart enumeration
  QUANTIFIERS_SYGUS_SMART_BLOCK_ANY_CONSTANT,
  // incomplete due to counterexample-guided instantiation not being complete
  QUANTIFIERS_CEGQI,
  // incomplete due to finite model finding not being complete
  QUANTIFIERS_FMF,
  // incomplete due to explicitly recorded instantiations
  QUANTIFIERS_RECORDED_INST,
  // incomplete due to limited number of allowed instantiation rounds
  QUANTIFIERS_MAX_INST_ROUNDS,
  // we solved a negated synthesis conjecture and will terminate as a subsolver
  // with unknown
  QUANTIFIERS_SYGUS_SOLVED,
  // incomplete due to separation logic
  SEP,
  // Higher order operators like sets.map were used in combination with set
  // cardinality constraints
  SETS_HO_CARD,
  // relations were used in combination with set cardinality constraints
  SETS_RELS_CARD,
  // we skipped processing a looping word equation
  STRINGS_LOOP_SKIP,
  // we could not simplify a regular expression membership
  STRINGS_REGEXP_NO_SIMPLIFY,
  // incomplete due to sequence of a dynamic finite type (e.g. a type that
  // we know is finite, but its exact cardinality is not fixed. For example,
  // when finite model finding is enabled, uninterpreted sorts have a
  // cardinality that depends on their interpretation in the current model).
  SEQ_FINITE_DYNAMIC_CARDINALITY,
  // HO extensionality axiom was disabled
  UF_HO_EXT_DISABLED,
  // UF+cardinality solver was disabled
  UF_CARD_DISABLED,
  // UF+cardinality solver used in an incomplete mode
  UF_CARD_MODE,

  //------------------- other causes external to theory engine
  // the prop layer stopped search
  STOP_SEARCH,
  //------------------- unknown
  UNKNOWN,
  NONE
};

/**
 * Converts an incompleteness id to a string.
 *
 * @param i The incompleteness identifier
 * @return The name of the incompleteness identifier
 */
const char* toString(IncompleteId i);

/**
 * Writes an incompleteness identifier to a stream.
 *
 * @param out The stream to write to
 * @param i The incompleteness identifier to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, IncompleteId i);

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__INCOMPLETE_ID_H */
