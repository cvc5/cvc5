/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof rule.
 */

#include <cvc5/cvc5_skolem_id.h>

#include <iostream>

namespace cvc5 {

const char* toString(SkolemFunId id)
{
  switch (id)
  {
    case SkolemFunId::INPUT_VARIABLE: return "INPUT_VARIABLE";
    case SkolemFunId::PURIFY: return "PURIFY";
    case SkolemFunId::ARRAY_DEQ_DIFF: return "ARRAY_DEQ_DIFF";
    case SkolemFunId::DIV_BY_ZERO: return "DIV_BY_ZERO";
    case SkolemFunId::INT_DIV_BY_ZERO: return "INT_DIV_BY_ZERO";
    case SkolemFunId::MOD_BY_ZERO: return "MOD_BY_ZERO";
    case SkolemFunId::SQRT: return "SQRT";
    case SkolemFunId::TRANSCENDENTAL_PURIFY_ARG:
      return "TRANSCENDENTAL_PURIFY_ARG";
    case SkolemFunId::SHARED_SELECTOR: return "SHARED_SELECTOR";
    case SkolemFunId::QUANTIFIERS_SKOLEMIZE: return "QUANTIFIERS_SKOLEMIZE";
    case SkolemFunId::QUANTIFIERS_SYNTH_FUN_EMBED:
      return "QUANTIFIERS_SYNTH_FUN_EMBED";
    case SkolemFunId::STRINGS_NUM_OCCUR: return "STRINGS_NUM_OCCUR";
    case SkolemFunId::STRINGS_NUM_OCCUR_RE: return "STRINGS_NUM_OCCUR_RE";
    case SkolemFunId::STRINGS_OCCUR_INDEX: return "STRINGS_OCCUR_INDEX";
    case SkolemFunId::STRINGS_OCCUR_INDEX_RE: return "STRINGS_OCCUR_INDEX_RE";
    case SkolemFunId::STRINGS_OCCUR_LEN: return "STRINGS_OCCUR_LEN";
    case SkolemFunId::STRINGS_OCCUR_LEN_RE: return "STRINGS_OCCUR_LEN_RE";
    case SkolemFunId::STRINGS_DEQ_DIFF: return "STRINGS_DEQ_DIFF";
    case SkolemFunId::STRINGS_REPLACE_ALL_RESULT:
      return "STRINGS_REPLACE_ALL_RESULT";
    case SkolemFunId::STRINGS_ITOS_RESULT: return "STRINGS_ITOS_RESULT";
    case SkolemFunId::STRINGS_STOI_RESULT: return "STRINGS_STOI_RESULT";
    case SkolemFunId::STRINGS_STOI_NON_DIGIT: return "STRINGS_STOI_NON_DIGIT";
    case SkolemFunId::RE_FIRST_MATCH_PRE: return "RE_FIRST_MATCH_PRE";
    case SkolemFunId::RE_FIRST_MATCH: return "RE_FIRST_MATCH";
    case SkolemFunId::RE_FIRST_MATCH_POST: return "RE_FIRST_MATCH_POST";
    case SkolemFunId::RE_UNFOLD_POS_COMPONENT: return "RE_UNFOLD_POS_COMPONENT";
    case SkolemFunId::SEQ_MODEL_BASE_ELEMENT: return "SEQ_MODEL_BASE_ELEMENT";
    case SkolemFunId::BAGS_CARD_CARDINALITY: return "BAGS_CARD_CARDINALITY";
    case SkolemFunId::BAGS_CARD_ELEMENTS: return "BAGS_CARD_ELEMENTS";
    case SkolemFunId::BAGS_CARD_N: return "BAGS_CARD_N";
    case SkolemFunId::BAGS_CARD_UNION_DISJOINT:
      return "BAGS_CARD_UNION_DISJOINT";
    case SkolemFunId::BAGS_CHOOSE: return "BAGS_CHOOSE";
    case SkolemFunId::BAGS_FOLD_CARD: return "BAGS_FOLD_CARD";
    case SkolemFunId::BAGS_FOLD_COMBINE: return "BAGS_FOLD_COMBINE";
    case SkolemFunId::BAGS_FOLD_ELEMENTS: return "BAGS_FOLD_ELEMENTS";
    case SkolemFunId::BAGS_FOLD_UNION_DISJOINT:
      return "BAGS_FOLD_UNION_DISJOINT";
    case SkolemFunId::BAGS_MAP_PREIMAGE: return "BAGS_MAP_PREIMAGE";
    case SkolemFunId::BAGS_MAP_PREIMAGE_SIZE: return "BAGS_MAP_PREIMAGE_SIZE";
    case SkolemFunId::BAGS_MAP_PREIMAGE_INDEX: return "BAGS_MAP_PREIMAGE_INDEX";
    case SkolemFunId::BAGS_MAP_SUM: return "BAGS_MAP_SUM";
    case SkolemFunId::BAGS_DEQ_DIFF: return "BAGS_DEQ_DIFF";
    case SkolemFunId::TABLES_GROUP_PART: return "TABLES_GROUP_PART";
    case SkolemFunId::TABLES_GROUP_PART_ELEMENT:
      return "TABLES_GROUP_PART_ELEMENT";
    case SkolemFunId::RELATIONS_GROUP_PART: return "RELATIONS_GROUP_PART";
    case SkolemFunId::RELATIONS_GROUP_PART_ELEMENT:
      return "RELATIONS_GROUP_PART_ELEMENT";
    case SkolemFunId::SETS_CHOOSE: return "SETS_CHOOSE";
    case SkolemFunId::SETS_DEQ_DIFF: return "SETS_DEQ_DIFF";
    case SkolemFunId::SETS_FOLD_CARD: return "SETS_FOLD_CARD";
    case SkolemFunId::SETS_FOLD_COMBINE: return "SETS_FOLD_COMBINE";
    case SkolemFunId::SETS_FOLD_ELEMENTS: return "SETS_FOLD_ELEMENTS";
    case SkolemFunId::SETS_FOLD_UNION: return "SETS_FOLD_UNION";
    case SkolemFunId::SETS_MAP_DOWN_ELEMENT: return "SETS_MAP_DOWN_ELEMENT";
    case SkolemFunId::HO_TYPE_MATCH_PRED: return "HO_TYPE_MATCH_PRED";
    case SkolemFunId::IEVAL_NONE: return "IEVAL_NONE";
    case SkolemFunId::IEVAL_SOME: return "IEVAL_SOME";
    case SkolemFunId::ABSTRACT_VALUE: return "ABSTRACT_VALUE";
    case SkolemFunId::SYGUS_ANY_CONSTANT: return "SYGUS_ANY_CONSTANT";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, SkolemFunId id)
{
  out << toString(id);
  return out;
}
}  // namespace cvc5

namespace std {

size_t hash<cvc5::SkolemFunId>::operator()(cvc5::SkolemFunId id) const
{
  return static_cast<size_t>(id);
}

}  // namespace std
