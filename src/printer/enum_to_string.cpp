/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utilities for printing API enum values.
 */

#include "printer/enum_to_string.h"

namespace cvc5::internal {

const char* toString(cvc5::SkolemFunId id)
{
  switch (id)
  {
    case cvc5::SkolemFunId::INTERNAL: return "INTERNAL";
    case cvc5::SkolemFunId::INPUT_VARIABLE: return "INPUT_VARIABLE";
    case cvc5::SkolemFunId::PURIFY: return "PURIFY";
    case cvc5::SkolemFunId::ARRAY_DEQ_DIFF: return "ARRAY_DEQ_DIFF";
    case cvc5::SkolemFunId::DIV_BY_ZERO: return "DIV_BY_ZERO";
    case cvc5::SkolemFunId::INT_DIV_BY_ZERO: return "INT_DIV_BY_ZERO";
    case cvc5::SkolemFunId::MOD_BY_ZERO: return "MOD_BY_ZERO";
    case cvc5::SkolemFunId::TRANSCENDENTAL_PURIFY:
      return "TRANSCENDENTAL_PURIFY";
    case cvc5::SkolemFunId::TRANSCENDENTAL_PURIFY_ARG:
      return "TRANSCENDENTAL_PURIFY_ARG";
    case cvc5::SkolemFunId::SHARED_SELECTOR: return "SHARED_SELECTOR";
    case cvc5::SkolemFunId::QUANTIFIERS_SKOLEMIZE:
      return "QUANTIFIERS_SKOLEMIZE";
    case cvc5::SkolemFunId::STRINGS_NUM_OCCUR: return "STRINGS_NUM_OCCUR";
    case cvc5::SkolemFunId::STRINGS_NUM_OCCUR_RE: return "STRINGS_NUM_OCCUR_RE";
    case cvc5::SkolemFunId::STRINGS_OCCUR_INDEX: return "STRINGS_OCCUR_INDEX";
    case cvc5::SkolemFunId::STRINGS_OCCUR_INDEX_RE:
      return "STRINGS_OCCUR_INDEX_RE";
    case cvc5::SkolemFunId::STRINGS_OCCUR_LEN_RE: return "STRINGS_OCCUR_LEN_RE";
    case cvc5::SkolemFunId::STRINGS_DEQ_DIFF: return "STRINGS_DEQ_DIFF";
    case cvc5::SkolemFunId::STRINGS_REPLACE_ALL_RESULT:
      return "STRINGS_REPLACE_ALL_RESULT";
    case cvc5::SkolemFunId::STRINGS_ITOS_RESULT: return "STRINGS_ITOS_RESULT";
    case cvc5::SkolemFunId::STRINGS_STOI_RESULT: return "STRINGS_STOI_RESULT";
    case cvc5::SkolemFunId::STRINGS_STOI_NON_DIGIT:
      return "STRINGS_STOI_NON_DIGIT";
    case cvc5::SkolemFunId::RE_FIRST_MATCH_PRE: return "RE_FIRST_MATCH_PRE";
    case cvc5::SkolemFunId::RE_FIRST_MATCH: return "RE_FIRST_MATCH";
    case cvc5::SkolemFunId::RE_FIRST_MATCH_POST: return "RE_FIRST_MATCH_POST";
    case cvc5::SkolemFunId::RE_UNFOLD_POS_COMPONENT:
      return "RE_UNFOLD_POS_COMPONENT";
    case cvc5::SkolemFunId::BAGS_CARD_COMBINE: return "BAGS_CARD_COMBINE";
    case cvc5::SkolemFunId::BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT:
      return "BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT";
    case cvc5::SkolemFunId::BAGS_CHOOSE: return "BAGS_CHOOSE";
    case cvc5::SkolemFunId::BAGS_FOLD_CARD: return "BAGS_FOLD_CARD";
    case cvc5::SkolemFunId::BAGS_FOLD_COMBINE: return "BAGS_FOLD_COMBINE";
    case cvc5::SkolemFunId::BAGS_FOLD_ELEMENTS: return "BAGS_FOLD_ELEMENTS";
    case cvc5::SkolemFunId::BAGS_FOLD_UNION_DISJOINT:
      return "BAGS_FOLD_UNION_DISJOINT";
    case cvc5::SkolemFunId::BAGS_DISTINCT_ELEMENTS:
      return "BAGS_DISTINCT_ELEMENTS";
    case cvc5::SkolemFunId::BAGS_MAP_PREIMAGE_INJECTIVE:
      return "BAGS_MAP_PREIMAGE_INJECTIVE";
    case cvc5::SkolemFunId::BAGS_DISTINCT_ELEMENTS_SIZE:
      return "BAGS_DISTINCT_ELEMENTS_SIZE";
    case cvc5::SkolemFunId::BAGS_MAP_INDEX: return "BAGS_MAP_INDEX";
    case cvc5::SkolemFunId::BAGS_MAP_SUM: return "BAGS_MAP_SUM";
    case cvc5::SkolemFunId::BAGS_DEQ_DIFF: return "BAGS_DEQ_DIFF";
    case cvc5::SkolemFunId::TABLES_GROUP_PART: return "TABLES_GROUP_PART";
    case cvc5::SkolemFunId::TABLES_GROUP_PART_ELEMENT:
      return "TABLES_GROUP_PART_ELEMENT";
    case cvc5::SkolemFunId::RELATIONS_GROUP_PART: return "RELATIONS_GROUP_PART";
    case cvc5::SkolemFunId::RELATIONS_GROUP_PART_ELEMENT:
      return "RELATIONS_GROUP_PART_ELEMENT";
    case cvc5::SkolemFunId::SETS_CHOOSE: return "SETS_CHOOSE";
    case cvc5::SkolemFunId::SETS_DEQ_DIFF: return "SETS_DEQ_DIFF";
    case cvc5::SkolemFunId::SETS_FOLD_CARD: return "SETS_FOLD_CARD";
    case cvc5::SkolemFunId::SETS_FOLD_COMBINE: return "SETS_FOLD_COMBINE";
    case cvc5::SkolemFunId::SETS_FOLD_ELEMENTS: return "SETS_FOLD_ELEMENTS";
    case cvc5::SkolemFunId::SETS_FOLD_UNION: return "SETS_FOLD_UNION";
    case cvc5::SkolemFunId::SETS_MAP_DOWN_ELEMENT:
      return "SETS_MAP_DOWN_ELEMENT";
    default: return "?";
  }
}

}  // namespace cvc5::internal
