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
  REAL_ALGEBRAIC_NUMBER_WITNESS,
  ARRAYS_EQ_RANGE,
  BAG_FIRST_INDEX,
  BAG_SECOND_INDEX,
  SET_FIRST_INDEX,
  SET_SECOND_INDEX,
  STRINGS_RE_ELIM_CONCAT_INDEX,
  STRINGS_RE_ELIM_STAR_INDEX,
  STRINGS_INDEX,
  STRINGS_LENGTH,
  STRINGS_SEQ_MODEL,
  STRINGS_VALUE_FOR_LENGTH,
  FUN_BOUND_VAR_LIST,
  QUANT_ELIM_SHADOW,
  QUANT_DT_EXPAND,
  QUANT_DT_SPLIT,
  QUANT_REW_PRENEX,
  QUANT_SYGUS_BUILTIN_FV,
};
/** Converts a bound variable identifier to a string. */
const char* toString(BoundVarId id);
/** Writes a bound variable identifier to a stream. */
std::ostream& operator<<(std::ostream& out, BoundVarId id);

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__BOUND_VAR_ID_H */
