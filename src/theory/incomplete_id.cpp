/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of incompleteness enumeration.
 */

#include "theory/incomplete_id.h"

#include <iostream>

namespace cvc5::internal {
namespace theory {

const char* toString(IncompleteId i)
{
  switch (i)
  {
    case IncompleteId::ARITH_NL_DISABLED: return "ARITH_NL_DISABLED";
    case IncompleteId::ARITH_NL: return "ARITH_NL";
    case IncompleteId::QUANTIFIERS: return "QUANTIFIERS";
    case IncompleteId::QUANTIFIERS_SYGUS_NO_VERIFY:
      return "QUANTIFIERS_SYGUS_NO_VERIFY";
    case IncompleteId::QUANTIFIERS_SYGUS_SMART_BLOCK_ANY_CONSTANT:
      return "QUANTIFIERS_SYGUS_SMART_BLOCK_ANY_CONSTANT";
    case IncompleteId::QUANTIFIERS_CEGQI: return "QUANTIFIERS_CEGQI";
    case IncompleteId::QUANTIFIERS_FMF: return "QUANTIFIERS_FMF";
    case IncompleteId::QUANTIFIERS_RECORDED_INST:
      return "QUANTIFIERS_RECORDED_INST";
    case IncompleteId::QUANTIFIERS_MAX_INST_ROUNDS:
      return "QUANTIFIERS_MAX_INST_ROUNDS";
    case IncompleteId::QUANTIFIERS_SYGUS_SOLVED:
      return "QUANTIFIERS_SYGUS_SOLVED";
    case IncompleteId::SEP: return "SEP";
    case IncompleteId::SETS_HO_CARD: return "SETS_HO_CARD";
    case IncompleteId::SETS_RELS_CARD: return "SETS_RELS_CARD";
    case IncompleteId::STRINGS_LOOP_SKIP: return "STRINGS_LOOP_SKIP";
    case IncompleteId::STRINGS_REGEXP_NO_SIMPLIFY:
      return "STRINGS_REGEXP_NO_SIMPLIFY";
    case IncompleteId::SEQ_FINITE_DYNAMIC_CARDINALITY:
      return "SEQ_FINITE_DYNAMIC_CARDINALITY";
    case IncompleteId::UF_HO_EXT_DISABLED: return "UF_HO_EXT_DISABLED";
    case IncompleteId::UF_CARD_DISABLED: return "UF_CARD_DISABLED";
    case IncompleteId::UF_CARD_MODE: return "UF_CARD_MODE";
    case IncompleteId::STOP_SEARCH: return "STOP_SEARCH";
    case IncompleteId::UNKNOWN: return "UNKNOWN";
    case IncompleteId::NONE: return "NONE";
    default: return "?IncompleteId?";
  }
}

std::ostream& operator<<(std::ostream& out, IncompleteId i)
{
  out << toString(i);
  return out;
}

}  // namespace theory
}  // namespace cvc5::internal
