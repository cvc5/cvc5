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
    case BoundVarId::REAL_ALGEBRAIC_NUMBER_WITNESS:return "REAL_ALGEBRAIC_NUMBER_WITNESS";
    case BoundVarId::ARRAYS_EQ_RANGE:return "ARRAYS_EQ_RANGE";
    case BoundVarId::BAG_FIRST_INDEX:return "BAG_FIRST_INDEX";
    case BoundVarId::BAG_SECOND_INDEX:return "BAG_SECOND_INDEX";
    case BoundVarId::SET_FIRST_INDEX:return "SET_FIRST_INDEX";
    case BoundVarId::SET_SECOND_INDEX:return "SET_SECOND_INDEX";
    case BoundVarId::STRINGS_RE_ELIM_CONCAT_INDEX:return "STRINGS_RE_ELIM_CONCAT_INDEX";
    case BoundVarId::STRINGS_RE_ELIM_STAR_INDEX:return "STRINGS_RE_ELIM_STAR_INDEX";
    case BoundVarId::STRINGS_INDEX:return "STRINGS_INDEX";
    case BoundVarId::STRINGS_LENGTH:return "STRINGS_LENGTH";
    case BoundVarId::STRINGS_SEQ_MODEL:return "STRINGS_SEQ_MODEL";
    case BoundVarId::STRINGS_VALUE_FOR_LENGTH:return "STRINGS_VALUE_FOR_LENGTH";
    case BoundVarId::FUN_BOUND_VAR_LIST:return "FUN_BOUND_VAR_LIST";
    case BoundVarId::QUANT_ELIM_SHADOW:return "QUANT_ELIM_SHADOW";
    case BoundVarId::QUANT_DT_EXPAND:return "QUANT_DT_EXPAND";
    case BoundVarId::QUANT_DT_SPLIT:return "QUANT_DT_SPLIT";
    case BoundVarId::QUANT_REW_PRENEX:return "QUANT_REW_PRENEX";
    case BoundVarId::QUANT_SYGUS_BUILTIN_FV:return "QUANT_SYGUS_BUILTIN_FV";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, BoundVarId id)
{
  out << toString(id);
  return out;
}

}  // namespace cvc5::internal
