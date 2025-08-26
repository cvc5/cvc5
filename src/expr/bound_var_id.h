/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Mathias Preiner
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
  /**
   * A bound variable corresponding to the universally quantified integer
   * variable used to range over (may be distinct) elements in a set, used
   * for axiomatizing the behavior of some term.
   * If there are multiple quantifiers, this variable should be the first one.
   */
  SETS_FIRST_INDEX,
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
  /**
   * A bound variable quantifying over all strings to reduce a regular
   * expression equality.
   */
  STRINGS_REG_EXP_EQ,

  /**
   * A unique (bound variable) which corresponds to
   * unique element values used in sequence models. See use in
   * TheoryStrings::collectModelValues.
   */
  STRINGS_SEQ_MODEL,
  /**
   * Mapping to the variable used for binding the witness term for the
   * EXISTS_STRING_LENGTH.
   */
  STRINGS_VALUE_FOR_LENGTH,
  /**
   * Constructing a unique bound variable list for a lambda
   * corresponding to an array constant.
   */
  FUN_BOUND_VAR_LIST,
  /**
   * Cached on (q, q', v), which is used to replace a
   * shadowed variable v, which is quantified by a subformula q' of quantified
   * formula q. Shadowed variables may be introduced when e.g. quantified
   * formulas appear on the right hand sides of substitutions in preprocessing.
   * They are eliminated by the rewriter.
   */
  ELIM_SHADOW,
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
  /**
   * A variable used by the valid witness proof generator. This is cached based
   * on the skolem that witnesses the variable, whose skolem identifier is one
   * of WITNESS_*.
   */
  VALID_WITNESS_VAR,
};
/** Converts a bound variable identifier to a string. */
const char* toString(BoundVarId id);
/** Writes a bound variable identifier to a stream. */
std::ostream& operator<<(std::ostream& out, BoundVarId id);

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__BOUND_VAR_ID_H */
