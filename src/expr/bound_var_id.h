/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bound variable identifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__BOUND_VAR_ID_H
#define CVC5__EXPR__BOUND_VAR_ID_H

#include <string>

namespace cvc5::internal {

/**
 * Bound variable identifiers. These are identifiers for constructing
 * canonical free variables internally.
 */
enum class BoundVarId
{
  NONE,
/**
 * A bound variable for the witness term used to eliminate real algebraic
 * numbers.
 */
  REAL_ALGEBRAIC_NUMBER_WITNESS,
/**
 * A bound variable used for transcendental function purification.
 */
  ARITH_TR_PURIFY,
/**
 * A bound variable corresponding to the index used in the eqrange expansion.
 */
  ARRAYS_EQ_RANGE,
/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over (may be distinct) elements in a bag, used
 * for axiomatizing the behavior of some term.
 * If there are multiple quantifiers, this variable should be the first one.
 */
  BAGS_FIRST_INDEX,
/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over (may be distinct) elements in a bag, used
 * for axiomatizing the behavior of some term.
 * This variable should be the second of multiple quantifiers.
 */
  BAGS_SECOND_INDEX,
  SETS_FIRST_INDEX,
  SETS_SECOND_INDEX,
  /**
 * Attributes used for constructing unique bound variables. The following
 * attributes are used to construct (deterministic) bound variables for
 * eliminations within eliminateConcat and eliminateStar respectively.
 */  
  STRINGS_RE_ELIM_CONCAT_INDEX,
  STRINGS_RE_ELIM_STAR_INDEX,
/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the valid positions in a string, used
 * for axiomatizing the behavior of some term.
 */
  STRINGS_INDEX,
/**
 * A bound variable corresponding to the universally quantified integer
 * variable used to range over the valid lengths of a string, used for
 * axiomatizing the behavior of some term.
 */
  STRINGS_LENGTH,
  STRINGS_SEQ_MODEL,
  STRINGS_VALUE_FOR_LENGTH,
  FUN_BOUND_VAR_LIST,
  QUANT_ELIM_SHADOW,
/**
 * Cached on (F, lit, a) where lit is the tested
 * literal used for expanding a quantified datatype variable in quantified
 * formula with body F, and a is the rational corresponding to the argument
 * position of the variable, e.g. lit is ((_ is C) x) and x is
 * replaced by (C y1 ... yn), where the argument position of yi is i.
 */
  QUANT_DT_EXPAND,
  /**
   * Cached on (q, v, i) where QuantDSplit::split is called
 * to split the variable v of q. We introduce bound variables, where the i^th
 * variable created in that method is cached based on i.
   */
  QUANT_DT_SPLIT,
/**
 * Cached on (v, q, i) where q is being miniscoped
 * for F_i in its body (and F_1 ... F_n), and v is one of the bound variables
 * that q binds.
 */
  QUANT_REW_MINISCOPE,
/**
 * Cached on (v, body) where we are prenexing bound
 * variable v in a nested quantified formula within the given body.
 */
  QUANT_REW_PRENEX,
/** Mapping sygus variables to builtin variables */
  QUANT_SYGUS_BUILTIN_FV,
};
/** Converts a bound variable identifier to a string. */
const char* toString(BoundVarId id);
/** Writes a bound variable identifier to a stream. */
std::ostream& operator<<(std::ostream& out, BoundVarId id);

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__BOUND_VAR_ID_H */
