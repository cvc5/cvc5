/*********************                                                        */
/*! \file inference_id.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference enumeration.
 **/

#include "theory/inference_id.h"

namespace CVC4 {
namespace theory {

const char* toString(InferenceId i)
{
  switch (i)
  {
    case InferenceId::ARITH_PP_ELIM_OPERATORS: return "ARITH_PP_ELIM_OPERATORS";
    case InferenceId::ARITH_NL_CONGRUENCE: return "ARITH_NL_CONGRUENCE";
    case InferenceId::ARITH_NL_SHARED_TERM_VALUE_SPLIT:
      return "ARITH_NL_SHARED_TERM_VALUE_SPLIT";
    case InferenceId::ARITH_NL_CM_QUADRATIC_EQ:
      return "ARITH_NL_CM_QUADRATIC_EQ";
    case InferenceId::ARITH_NL_SPLIT_ZERO: return "ARITH_NL_SPLIT_ZERO";
    case InferenceId::ARITH_NL_SIGN: return "ARITH_NL_SIGN";
    case InferenceId::ARITH_NL_COMPARISON: return "ARITH_NL_COMPARISON";
    case InferenceId::ARITH_NL_INFER_BOUNDS: return "ARITH_NL_INFER_BOUNDS";
    case InferenceId::ARITH_NL_INFER_BOUNDS_NT:
      return "ARITH_NL_INFER_BOUNDS_NT";
    case InferenceId::ARITH_NL_FACTOR: return "ARITH_NL_FACTOR";
    case InferenceId::ARITH_NL_RES_INFER_BOUNDS:
      return "ARITH_NL_RES_INFER_BOUNDS";
    case InferenceId::ARITH_NL_TANGENT_PLANE: return "ARITH_NL_TANGENT_PLANE";
    case InferenceId::ARITH_NL_T_PURIFY_ARG: return "ARITH_NL_T_PURIFY_ARG";
    case InferenceId::ARITH_NL_T_INIT_REFINE: return "ARITH_NL_T_INIT_REFINE";
    case InferenceId::ARITH_NL_T_PI_BOUND: return "ARITH_NL_T_PI_BOUND";
    case InferenceId::ARITH_NL_T_MONOTONICITY: return "ARITH_NL_T_MONOTONICITY";
    case InferenceId::ARITH_NL_T_SECANT: return "ARITH_NL_T_SECANT";
    case InferenceId::ARITH_NL_T_TANGENT: return "ARITH_NL_T_TANGENT";
    case InferenceId::ARITH_NL_IAND_INIT_REFINE:
      return "ARITH_NL_IAND_INIT_REFINE";
    case InferenceId::ARITH_NL_IAND_VALUE_REFINE:
      return "ARITH_NL_IAND_VALUE_REFINE";
    case InferenceId::ARITH_NL_IAND_SUM_REFINE:
      return "ARITH_NL_IAND_SUM_REFINE";
    case InferenceId::ARITH_NL_IAND_BITWISE_REFINE:
      return "ARITH_NL_IAND_BITWISE_REFINE";
    case InferenceId::ARITH_NL_CAD_CONFLICT: return "ARITH_NL_CAD_CONFLICT";
    case InferenceId::ARITH_NL_CAD_EXCLUDED_INTERVAL:
      return "ARITH_NL_CAD_EXCLUDED_INTERVAL";
    case InferenceId::ARITH_NL_ICP_CONFLICT: return "ARITH_NL_ICP_CONFLICT";
    case InferenceId::ARITH_NL_ICP_PROPAGATION:
      return "ARITH_NL_ICP_PROPAGATION";

    case InferenceId::ARRAYS_EXT: return "ARRAYS_EXT";
    case InferenceId::ARRAYS_READ_OVER_WRITE: return "ARRAYS_READ_OVER_WRITE";
    case InferenceId::ARRAYS_READ_OVER_WRITE_1: return "ARRAYS_READ_OVER_WRITE_1";
    case InferenceId::ARRAYS_READ_OVER_WRITE_CONTRA: return "ARRAYS_READ_OVER_WRITE_CONTRA";

    case InferenceId::BAG_NON_NEGATIVE_COUNT: return "BAG_NON_NEGATIVE_COUNT";
    case InferenceId::BAG_MK_BAG_SAME_ELEMENT: return "BAG_MK_BAG_SAME_ELEMENT";
    case InferenceId::BAG_MK_BAG: return "BAG_MK_BAG";
    case InferenceId::BAG_EQUALITY: return "BAG_EQUALITY";
    case InferenceId::BAG_DISEQUALITY: return "BAG_DISEQUALITY";
    case InferenceId::BAG_EMPTY: return "BAG_EMPTY";
    case InferenceId::BAG_UNION_DISJOINT: return "BAG_UNION_DISJOINT";
    case InferenceId::BAG_UNION_MAX: return "BAG_UNION_MAX";
    case InferenceId::BAG_INTERSECTION_MIN: return "BAG_INTERSECTION_MIN";
    case InferenceId::BAG_DIFFERENCE_SUBTRACT: return "BAG_DIFFERENCE_SUBTRACT";
    case InferenceId::BAG_DIFFERENCE_REMOVE: return "BAG_DIFFERENCE_REMOVE";
    case InferenceId::BAG_DUPLICATE_REMOVAL: return "BAG_DUPLICATE_REMOVAL";

    case InferenceId::DATATYPES_UNIF: return "UNIF";
    case InferenceId::DATATYPES_INST: return "INST";
    case InferenceId::DATATYPES_SPLIT: return "SPLIT";
    case InferenceId::DATATYPES_LABEL_EXH: return "LABEL_EXH";
    case InferenceId::DATATYPES_COLLAPSE_SEL: return "COLLAPSE_SEL";
    case InferenceId::DATATYPES_CLASH_CONFLICT: return "CLASH_CONFLICT";
    case InferenceId::DATATYPES_TESTER_CONFLICT: return "TESTER_CONFLICT";
    case InferenceId::DATATYPES_TESTER_MERGE_CONFLICT: return "TESTER_MERGE_CONFLICT";
    case InferenceId::DATATYPES_BISIMILAR: return "BISIMILAR";
    case InferenceId::DATATYPES_CYCLE: return "CYCLE";

    case InferenceId::SEP_PTO_NEG_PROP: return "SEP_PTO_NEG_PROP";
    case InferenceId::SEP_PTO_PROP: return "SEP_PTO_PROP";

    case InferenceId::SETS_COMPREHENSION: return "SETS_COMPREHENSION";
    case InferenceId::SETS_DEQ: return "SETS_DEQ";
    case InferenceId::SETS_DOWN_CLOSURE: return "SETS_DOWN_CLOSURE";
    case InferenceId::SETS_EQ_MEM: return "SETS_EQ_MEM";
    case InferenceId::SETS_EQ_MEM_CONFLICT: return "SETS_EQ_MEM_CONFLICT";
    case InferenceId::SETS_MEM_EQ: return "SETS_MEM_EQ";
    case InferenceId::SETS_MEM_EQ_CONFLICT: return "SETS_MEM_EQ_CONFLICT";
    case InferenceId::SETS_PROXY: return "SETS_PROXY";
    case InferenceId::SETS_PROXY_SINGLETON: return "SETS_PROXY_SINGLETON";
    case InferenceId::SETS_SINGLETON_EQ: return "SETS_SINGLETON_EQ";
    case InferenceId::SETS_UP_CLOSURE: return "SETS_UP_CLOSURE";
    case InferenceId::SETS_UP_CLOSURE_2: return "SETS_UP_CLOSURE_2";
    case InferenceId::SETS_UP_UNIV: return "SETS_UP_UNIV";
    case InferenceId::SETS_UNIV_TYPE: return "SETS_UNIV_TYPE";
    case InferenceId::SETS_CARD_CYCLE: return "SETS_CARD_CYCLE";
    case InferenceId::SETS_CARD_EQUAL: return "SETS_CARD_EQUAL";
    case InferenceId::SETS_CARD_GRAPH_EMP: return "SETS_CARD_GRAPH_EMP";
    case InferenceId::SETS_CARD_GRAPH_EMP_PARENT:
      return "SETS_CARD_GRAPH_EMP_PARENT";
    case InferenceId::SETS_CARD_GRAPH_EQ_PARENT:
      return "SETS_CARD_GRAPH_EQ_PARENT";
    case InferenceId::SETS_CARD_GRAPH_EQ_PARENT_2:
      return "SETS_CARD_GRAPH_EQ_PARENT_2";
    case InferenceId::SETS_CARD_GRAPH_PARENT_SINGLETON:
      return "SETS_CARD_GRAPH_PARENT_SINGLETON";
    case InferenceId::SETS_CARD_MINIMAL: return "SETS_CARD_MINIMAL";
    case InferenceId::SETS_CARD_NEGATIVE_MEMBER:
      return "SETS_CARD_NEGATIVE_MEMBER";
    case InferenceId::SETS_CARD_POSITIVE: return "SETS_CARD_POSITIVE";
    case InferenceId::SETS_CARD_UNIV_SUPERSET: return "SETS_CARD_UNIV_SUPERSET";
    case InferenceId::SETS_CARD_UNIV_TYPE: return "SETS_CARD_UNIV_TYPE";
    case InferenceId::SETS_RELS_IDENTITY_DOWN: return "SETS_RELS_IDENTITY_DOWN";
    case InferenceId::SETS_RELS_IDENTITY_UP: return "SETS_RELS_IDENTITY_UP";
    case InferenceId::SETS_RELS_JOIN_COMPOSE: return "SETS_RELS_JOIN_COMPOSE";
    case InferenceId::SETS_RELS_JOIN_IMAGE_DOWN:
      return "SETS_RELS_JOIN_IMAGE_DOWN";
    case InferenceId::SETS_RELS_JOIN_SPLIT_1: return "SETS_RELS_JOIN_SPLIT_1";
    case InferenceId::SETS_RELS_JOIN_SPLIT_2: return "SETS_RELS_JOIN_SPLIT_2";
    case InferenceId::SETS_RELS_PRODUCE_COMPOSE:
      return "SETS_RELS_PRODUCE_COMPOSE";
    case InferenceId::SETS_RELS_PRODUCT_SPLIT: return "SETS_RELS_PRODUCT_SPLIT";
    case InferenceId::SETS_RELS_TCLOSURE_FWD: return "SETS_RELS_TCLOSURE_FWD";
    case InferenceId::SETS_RELS_TRANSPOSE_EQ: return "SETS_RELS_TRANSPOSE_EQ";
    case InferenceId::SETS_RELS_TRANSPOSE_REV: return "SETS_RELS_TRANSPOSE_REV";
    case InferenceId::SETS_RELS_TUPLE_REDUCTION:
      return "SETS_RELS_TUPLE_REDUCTION";

    case InferenceId::STRINGS_I_NORM_S: return "I_NORM_S";
    case InferenceId::STRINGS_I_CONST_MERGE: return "I_CONST_MERGE";
    case InferenceId::STRINGS_I_CONST_CONFLICT: return "I_CONST_CONFLICT";
    case InferenceId::STRINGS_I_NORM: return "I_NORM";
    case InferenceId::STRINGS_UNIT_INJ: return "UNIT_INJ";
    case InferenceId::STRINGS_UNIT_CONST_CONFLICT: return "UNIT_CONST_CONFLICT";
    case InferenceId::STRINGS_UNIT_INJ_DEQ: return "UNIT_INJ_DEQ";
    case InferenceId::STRINGS_CARD_SP: return "CARD_SP";
    case InferenceId::STRINGS_CARDINALITY: return "CARDINALITY";
    case InferenceId::STRINGS_I_CYCLE_E: return "I_CYCLE_E";
    case InferenceId::STRINGS_I_CYCLE: return "I_CYCLE";
    case InferenceId::STRINGS_F_CONST: return "F_CONST";
    case InferenceId::STRINGS_F_UNIFY: return "F_UNIFY";
    case InferenceId::STRINGS_F_ENDPOINT_EMP: return "F_ENDPOINT_EMP";
    case InferenceId::STRINGS_F_ENDPOINT_EQ: return "F_ENDPOINT_EQ";
    case InferenceId::STRINGS_F_NCTN: return "F_NCTN";
    case InferenceId::STRINGS_N_EQ_CONF: return "N_EQ_CONF";
    case InferenceId::STRINGS_N_ENDPOINT_EMP: return "N_ENDPOINT_EMP";
    case InferenceId::STRINGS_N_UNIFY: return "N_UNIFY";
    case InferenceId::STRINGS_N_ENDPOINT_EQ: return "N_ENDPOINT_EQ";
    case InferenceId::STRINGS_N_CONST: return "N_CONST";
    case InferenceId::STRINGS_INFER_EMP: return "INFER_EMP";
    case InferenceId::STRINGS_SSPLIT_CST_PROP: return "SSPLIT_CST_PROP";
    case InferenceId::STRINGS_SSPLIT_VAR_PROP: return "SSPLIT_VAR_PROP";
    case InferenceId::STRINGS_LEN_SPLIT: return "LEN_SPLIT";
    case InferenceId::STRINGS_LEN_SPLIT_EMP: return "LEN_SPLIT_EMP";
    case InferenceId::STRINGS_SSPLIT_CST: return "SSPLIT_CST";
    case InferenceId::STRINGS_SSPLIT_VAR: return "SSPLIT_VAR";
    case InferenceId::STRINGS_FLOOP: return "FLOOP";
    case InferenceId::STRINGS_FLOOP_CONFLICT: return "FLOOP_CONFLICT";
    case InferenceId::STRINGS_NORMAL_FORM: return "NORMAL_FORM";
    case InferenceId::STRINGS_N_NCTN: return "N_NCTN";
    case InferenceId::STRINGS_LEN_NORM: return "LEN_NORM";
    case InferenceId::STRINGS_DEQ_DISL_EMP_SPLIT: return "DEQ_DISL_EMP_SPLIT";
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
      return "DEQ_DISL_FIRST_CHAR_EQ_SPLIT";
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
      return "DEQ_DISL_FIRST_CHAR_STRING_SPLIT";
    case InferenceId::STRINGS_DEQ_STRINGS_EQ: return "DEQ_STRINGS_EQ";
    case InferenceId::STRINGS_DEQ_DISL_STRINGS_SPLIT: return "DEQ_DISL_STRINGS_SPLIT";
    case InferenceId::STRINGS_DEQ_LENS_EQ: return "DEQ_LENS_EQ";
    case InferenceId::STRINGS_DEQ_NORM_EMP: return "DEQ_NORM_EMP";
    case InferenceId::STRINGS_DEQ_LENGTH_SP: return "DEQ_LENGTH_SP";
    case InferenceId::STRINGS_CODE_PROXY: return "CODE_PROXY";
    case InferenceId::STRINGS_CODE_INJ: return "CODE_INJ";
    case InferenceId::STRINGS_RE_NF_CONFLICT: return "RE_NF_CONFLICT";
    case InferenceId::STRINGS_RE_UNFOLD_POS: return "RE_UNFOLD_POS";
    case InferenceId::STRINGS_RE_UNFOLD_NEG: return "RE_UNFOLD_NEG";
    case InferenceId::STRINGS_RE_INTER_INCLUDE: return "RE_INTER_INCLUDE";
    case InferenceId::STRINGS_RE_INTER_CONF: return "RE_INTER_CONF";
    case InferenceId::STRINGS_RE_INTER_INFER: return "RE_INTER_INFER";
    case InferenceId::STRINGS_RE_DELTA: return "RE_DELTA";
    case InferenceId::STRINGS_RE_DELTA_CONF: return "RE_DELTA_CONF";
    case InferenceId::STRINGS_RE_DERIVE: return "RE_DERIVE";
    case InferenceId::STRINGS_EXTF: return "EXTF";
    case InferenceId::STRINGS_EXTF_N: return "EXTF_N";
    case InferenceId::STRINGS_EXTF_D: return "EXTF_D";
    case InferenceId::STRINGS_EXTF_D_N: return "EXTF_D_N";
    case InferenceId::STRINGS_EXTF_EQ_REW: return "EXTF_EQ_REW";
    case InferenceId::STRINGS_CTN_TRANS: return "CTN_TRANS";
    case InferenceId::STRINGS_CTN_DECOMPOSE: return "CTN_DECOMPOSE";
    case InferenceId::STRINGS_CTN_NEG_EQUAL: return "CTN_NEG_EQUAL";
    case InferenceId::STRINGS_CTN_POS: return "CTN_POS";
    case InferenceId::STRINGS_REDUCTION: return "REDUCTION";
    case InferenceId::STRINGS_PREFIX_CONFLICT: return "PREFIX_CONFLICT";

    case InferenceId::UF_HO_APP_ENCODE: return "UF_HO_APP_ENCODE";
    case InferenceId::UF_HO_APP_CONV_SKOLEM: return "UF_HO_APP_CONV_SKOLEM";
    case InferenceId::UF_HO_EXTENSIONALITY: return "UF_HO_EXTENSIONALITY";
    case InferenceId::UF_HO_MODEL_APP_ENCODE: return "UF_HO_MODEL_APP_ENCODE";
    case InferenceId::UF_HO_MODEL_EXTENSIONALITY:
      return "UF_HO_MODEL_EXTENSIONALITY";

    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, InferenceId i)
{
  out << toString(i);
  return out;
}

}  // namespace theory
}  // namespace CVC4
