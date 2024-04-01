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

const char* toString(cvc5::SkolemId id)
{
  switch (id)
  {
    case cvc5::SkolemId::INTERNAL: return "internal";
    case cvc5::SkolemId::PURIFY: return "purify";
    case cvc5::SkolemId::ARRAY_DEQ_DIFF: return "array_deq_diff";
    case cvc5::SkolemId::DIV_BY_ZERO: return "div_by_zero";
    case cvc5::SkolemId::INT_DIV_BY_ZERO: return "int_div_by_zero";
    case cvc5::SkolemId::MOD_BY_ZERO: return "mod_by_zero";
    case cvc5::SkolemId::TRANSCENDENTAL_PURIFY:
      return "transcendental_purify";
    case cvc5::SkolemId::TRANSCENDENTAL_PURIFY_ARG:
      return "transcendental_purify_arg";
    case cvc5::SkolemId::SHARED_SELECTOR: return "shared_selector";
    case cvc5::SkolemId::QUANTIFIERS_SKOLEMIZE:
      return "quantifiers_skolemize";
    case cvc5::SkolemId::STRINGS_NUM_OCCUR: return "strings_num_occur";
    case cvc5::SkolemId::STRINGS_NUM_OCCUR_RE: return "strings_num_occur_re";
    case cvc5::SkolemId::STRINGS_OCCUR_INDEX: return "strings_occur_index";
    case cvc5::SkolemId::STRINGS_OCCUR_INDEX_RE:
      return "strings_occur_index_re";
    case cvc5::SkolemId::STRINGS_OCCUR_LEN_RE: return "strings_occur_len_re";
    case cvc5::SkolemId::STRINGS_DEQ_DIFF: return "strings_deq_diff";
    case cvc5::SkolemId::STRINGS_REPLACE_ALL_RESULT:
      return "strings_replace_all_result";
    case cvc5::SkolemId::STRINGS_ITOS_RESULT: return "strings_itos_result";
    case cvc5::SkolemId::STRINGS_STOI_RESULT: return "strings_stoi_result";
    case cvc5::SkolemId::STRINGS_STOI_NON_DIGIT:
      return "strings_stoi_non_digit";
    case cvc5::SkolemId::RE_FIRST_MATCH_PRE: return "re_first_match_pre";
    case cvc5::SkolemId::RE_FIRST_MATCH: return "re_first_match";
    case cvc5::SkolemId::RE_FIRST_MATCH_POST: return "re_first_match_post";
    case cvc5::SkolemId::RE_UNFOLD_POS_COMPONENT:
      return "re_unfold_pos_component";
    case cvc5::SkolemId::BAGS_CARD_COMBINE: return "bags_card_combine";
    case cvc5::SkolemId::BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT:
      return "bags_distinct_elements_union_disjoint";
    case cvc5::SkolemId::BAGS_CHOOSE: return "bags_choose";
    case cvc5::SkolemId::BAGS_FOLD_CARD: return "bags_fold_card";
    case cvc5::SkolemId::BAGS_FOLD_COMBINE: return "bags_fold_combine";
    case cvc5::SkolemId::BAGS_FOLD_ELEMENTS: return "bags_fold_elements";
    case cvc5::SkolemId::BAGS_FOLD_UNION_DISJOINT:
      return "bags_fold_union_disjoint";
    case cvc5::SkolemId::BAGS_DISTINCT_ELEMENTS:
      return "bags_distinct_elements";
    case cvc5::SkolemId::BAGS_MAP_PREIMAGE_INJECTIVE:
      return "bags_map_preimage_injective";
    case cvc5::SkolemId::BAGS_DISTINCT_ELEMENTS_SIZE:
      return "bags_distinct_elements_size";
    case cvc5::SkolemId::BAGS_MAP_INDEX: return "bags_map_index";
    case cvc5::SkolemId::BAGS_MAP_SUM: return "bags_map_sum";
    case cvc5::SkolemId::BAGS_DEQ_DIFF: return "bags_deq_diff";
    case cvc5::SkolemId::TABLES_GROUP_PART: return "tables_group_part";
    case cvc5::SkolemId::TABLES_GROUP_PART_ELEMENT:
      return "tables_group_part_element";
    case cvc5::SkolemId::RELATIONS_GROUP_PART: return "relations_group_part";
    case cvc5::SkolemId::RELATIONS_GROUP_PART_ELEMENT:
      return "relations_group_part_element";
    case cvc5::SkolemId::SETS_CHOOSE: return "sets_choose";
    case cvc5::SkolemId::SETS_DEQ_DIFF: return "sets_deq_diff";
    case cvc5::SkolemId::SETS_FOLD_CARD: return "sets_fold_card";
    case cvc5::SkolemId::SETS_FOLD_COMBINE: return "sets_fold_combine";
    case cvc5::SkolemId::SETS_FOLD_ELEMENTS: return "sets_fold_elements";
    case cvc5::SkolemId::SETS_FOLD_UNION: return "sets_fold_union";
    case cvc5::SkolemId::SETS_MAP_DOWN_ELEMENT:
      return "sets_map_down_element";
    case cvc5::SkolemId::NONE: return "none";
    default: return "?";
  }
}

}  // namespace cvc5::internal
