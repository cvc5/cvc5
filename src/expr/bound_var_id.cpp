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
 * Implementation of bound variable identifiers.
 */

#include "expr/bound_var_id.h"

#include <sstream>

namespace cvc5::internal {

const char* toString(BoundVarId id)
{
  switch (id)
  {
    case BoundVarId::REAL_ALGEBRAIC_NUMBER_WITNESS:
      return "REAL_ALGEBRAIC_NUMBER_WITNESS";
    case BoundVarId::ARITH_TR_PURIFY: return "ARITH_TR_PURIFY";
    case BoundVarId::ARRAYS_EQ_RANGE: return "ARRAYS_EQ_RANGE";
    case BoundVarId::BAGS_FIRST_INDEX: return "BAGS_FIRST_INDEX";
    case BoundVarId::BAGS_SECOND_INDEX: return "BAGS_SECOND_INDEX";
    case BoundVarId::SETS_FIRST_INDEX: return "SETS_FIRST_INDEX";
    case BoundVarId::STRINGS_RE_ELIM_CONCAT_INDEX:
      return "STRINGS_RE_ELIM_CONCAT_INDEX";
    case BoundVarId::STRINGS_RE_ELIM_STAR_INDEX:
      return "STRINGS_RE_ELIM_STAR_INDEX";
    case BoundVarId::STRINGS_INDEX: return "STRINGS_INDEX";
    case BoundVarId::STRINGS_LENGTH: return "STRINGS_LENGTH";
    case BoundVarId::STRINGS_REG_EXP_EQ: return "STRINGS_REG_EXP_EQ";
    case BoundVarId::STRINGS_SEQ_MODEL: return "STRINGS_SEQ_MODEL";
    case BoundVarId::STRINGS_VALUE_FOR_LENGTH:
      return "STRINGS_VALUE_FOR_LENGTH";
    case BoundVarId::FUN_BOUND_VAR_LIST: return "FUN_BOUND_VAR_LIST";
    case BoundVarId::ELIM_SHADOW: return "ELIM_SHADOW";
    case BoundVarId::QUANT_DT_EXPAND: return "QUANT_DT_EXPAND";
    case BoundVarId::QUANT_DT_SPLIT: return "QUANT_DT_SPLIT";
    case BoundVarId::QUANT_REW_MINISCOPE: return "QUANT_REW_MINISCOPE";
    case BoundVarId::QUANT_REW_PRENEX: return "QUANT_REW_PRENEX";
    case BoundVarId::QUANT_SYGUS_BUILTIN_FV: return "QUANT_SYGUS_BUILTIN_FV";
    case BoundVarId::VALID_WITNESS_VAR: return "VALID_WITNESS_VAR";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, BoundVarId id)
{
  out << toString(id);
  return out;
}

}  // namespace cvc5::internal
