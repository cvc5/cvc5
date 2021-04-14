/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference enumeration.
 */

#include "theory/inference_id.h"

#include <iostream>

namespace cvc5 {
namespace theory {

const char* toString(InferenceId i)
{
  switch (i)
  {
    case InferenceId::EQ_CONSTANT_MERGE: return "EQ_CONSTANT_MERGE";
    case InferenceId::ARITH_BLACK_BOX: return "ARITH_BLACK_BOX";
    case InferenceId::ARITH_CONF_EQ: return "ARITH_CONF_EQ";
    case InferenceId::ARITH_CONF_LOWER: return "ARITH_CONF_LOWER";
    case InferenceId::ARITH_CONF_TRICHOTOMY: return "ARITH_CONF_TRICHOTOMY";
    case InferenceId::ARITH_CONF_UPPER: return "ARITH_CONF_UPPER";
    case InferenceId::ARITH_CONF_SIMPLEX: return "ARITH_CONF_SIMPLEX";
    case InferenceId::ARITH_CONF_SOI_SIMPLEX: return "ARITH_CONF_SOI_SIMPLEX";
    case InferenceId::ARITH_SPLIT_DEQ: return "ARITH_SPLIT_DEQ";
    case InferenceId::ARITH_TIGHTEN_CEIL: return "ARITH_TIGHTEN_CEIL";
    case InferenceId::ARITH_TIGHTEN_FLOOR: return "ARITH_TIGHTEN_FLOOR";
    case InferenceId::ARITH_APPROX_CUT: return "ARITH_APPROX_CUT";
    case InferenceId::ARITH_BB_LEMMA: return "ARITH_BB_LEMMA";
    case InferenceId::ARITH_DIO_CUT: return "ARITH_DIO_CUT";
    case InferenceId::ARITH_DIO_DECOMPOSITION: return "ARITH_DIO_DECOMPOSITION";
    case InferenceId::ARITH_SPLIT_FOR_NL_MODEL:
      return "ARITH_SPLIT_FOR_NL_MODEL";
    case InferenceId::ARITH_PP_ELIM_OPERATORS: return "ARITH_PP_ELIM_OPERATORS";
    case InferenceId::ARITH_PP_ELIM_OPERATORS_LEMMA:
      return "ARITH_PP_ELIM_OPERATORS_LEMMA";
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

    case InferenceId::BV_BITBLAST_CONFLICT: return "BV_BITBLAST_CONFLICT";
    case InferenceId::BV_LAZY_CONFLICT: return "BV_LAZY_CONFLICT";
    case InferenceId::BV_LAZY_LEMMA: return "BV_LAZY_LEMMA";
    case InferenceId::BV_SIMPLE_LEMMA: return "BV_SIMPLE_LEMMA";
    case InferenceId::BV_SIMPLE_BITBLAST_LEMMA: return "BV_SIMPLE_BITBLAST_LEMMA";
    case InferenceId::BV_EXTF_LEMMA: return "BV_EXTF_LEMMA";
    case InferenceId::BV_EXTF_COLLAPSE: return "BV_EXTF_COLLAPSE";

    case InferenceId::DATATYPES_PURIFY: return "DATATYPES_PURIFY";
    case InferenceId::DATATYPES_UNIF: return "DATATYPES_UNIF";
    case InferenceId::DATATYPES_INST: return "DATATYPES_INST";
    case InferenceId::DATATYPES_SPLIT: return "DATATYPES_SPLIT";
    case InferenceId::DATATYPES_BINARY_SPLIT: return "DATATYPES_BINARY_SPLIT";
    case InferenceId::DATATYPES_LABEL_EXH: return "DATATYPES_LABEL_EXH";
    case InferenceId::DATATYPES_COLLAPSE_SEL: return "DATATYPES_COLLAPSE_SEL";
    case InferenceId::DATATYPES_CLASH_CONFLICT:
      return "DATATYPES_CLASH_CONFLICT";
    case InferenceId::DATATYPES_TESTER_CONFLICT:
      return "DATATYPES_TESTER_CONFLICT";
    case InferenceId::DATATYPES_TESTER_MERGE_CONFLICT:
      return "DATATYPES_TESTER_MERGE_CONFLICT";
    case InferenceId::DATATYPES_BISIMILAR: return "DATATYPES_BISIMILAR";
    case InferenceId::DATATYPES_REC_SINGLETON_EQ:
      return "DATATYPES_REC_SINGLETON_EQ";
    case InferenceId::DATATYPES_REC_SINGLETON_FORCE_DEQ:
      return "DATATYPES_REC_SINGLETON_FORCE_DEQ";
    case InferenceId::DATATYPES_CYCLE: return "DATATYPES_CYCLE";
    case InferenceId::DATATYPES_SIZE_POS: return "DATATYPES_SIZE_POS";
    case InferenceId::DATATYPES_HEIGHT_ZERO: return "DATATYPES_HEIGHT_ZERO";
    case InferenceId::DATATYPES_SYGUS_SYM_BREAK:
      return "DATATYPES_SYGUS_SYM_BREAK";
    case InferenceId::DATATYPES_SYGUS_CDEP_SYM_BREAK:
      return "DATATYPES_SYGUS_CDEP_SYM_BREAK";
    case InferenceId::DATATYPES_SYGUS_ENUM_SYM_BREAK:
      return "DATATYPES_SYGUS_ENUM_SYM_BREAK";
    case InferenceId::DATATYPES_SYGUS_SIMPLE_SYM_BREAK:
      return "DATATYPES_SYGUS_SIMPLE_SYM_BREAK";
    case InferenceId::DATATYPES_SYGUS_FAIR_SIZE:
      return "DATATYPES_SYGUS_FAIR_SIZE";
    case InferenceId::DATATYPES_SYGUS_FAIR_SIZE_CONFLICT:
      return "DATATYPES_SYGUS_FAIR_SIZE_CONFLICT";
    case InferenceId::DATATYPES_SYGUS_VAR_AGNOSTIC:
      return "DATATYPES_SYGUS_VAR_AGNOSTIC";
    case InferenceId::DATATYPES_SYGUS_SIZE_CORRECTION:
      return "DATATYPES_SYGUS_SIZE_CORRECTION";
    case InferenceId::DATATYPES_SYGUS_VALUE_CORRECTION:
      return "DATATYPES_SYGUS_VALUE_CORRECTION";
    case InferenceId::DATATYPES_SYGUS_MT_BOUND:
      return "DATATYPES_SYGUS_MT_BOUND";
    case InferenceId::DATATYPES_SYGUS_MT_POS: return "DATATYPES_SYGUS_MT_POS";

    case InferenceId::QUANTIFIERS_INST_E_MATCHING:
      return "QUANTIFIERS_INST_E_MATCHING";
    case InferenceId::QUANTIFIERS_INST_E_MATCHING_SIMPLE:
      return "QUANTIFIERS_INST_E_MATCHING_SIMPLE";
    case InferenceId::QUANTIFIERS_INST_E_MATCHING_MT:
      return "QUANTIFIERS_INST_E_MATCHING_MT";
    case InferenceId::QUANTIFIERS_INST_E_MATCHING_MTL:
      return "QUANTIFIERS_INST_E_MATCHING_MTL";
    case InferenceId::QUANTIFIERS_INST_E_MATCHING_HO:
      return "QUANTIFIERS_INST_E_MATCHING_HO";
    case InferenceId::QUANTIFIERS_INST_E_MATCHING_VAR_GEN:
      return "QUANTIFIERS_INST_E_MATCHING_VAR_GEN";
    case InferenceId::QUANTIFIERS_INST_CBQI_CONFLICT:
      return "QUANTIFIERS_INST_CBQI_CONFLICT";
    case InferenceId::QUANTIFIERS_INST_CBQI_PROP:
      return "QUANTIFIERS_INST_CBQI_PROP";
    case InferenceId::QUANTIFIERS_INST_FMF_EXH:
      return "QUANTIFIERS_INST_FMF_EXH";
    case InferenceId::QUANTIFIERS_INST_FMF_FMC:
      return "QUANTIFIERS_INST_FMF_FMC";
    case InferenceId::QUANTIFIERS_INST_FMF_FMC_EXH:
      return "QUANTIFIERS_INST_FMF_FMC_EXH";
    case InferenceId::QUANTIFIERS_INST_CEGQI: return "QUANTIFIERS_INST_CEGQI";
    case InferenceId::QUANTIFIERS_INST_SYQI: return "QUANTIFIERS_INST_SYQI";
    case InferenceId::QUANTIFIERS_INST_ENUM: return "QUANTIFIERS_INST_ENUM";
    case InferenceId::QUANTIFIERS_INST_POOL: return "QUANTIFIERS_INST_POOL";
    case InferenceId::QUANTIFIERS_BINT_PROXY: return "QUANTIFIERS_BINT_PROXY";
    case InferenceId::QUANTIFIERS_BINT_MIN_NG: return "QUANTIFIERS_BINT_MIN_NG";
    case InferenceId::QUANTIFIERS_CEGQI_CEX: return "QUANTIFIERS_CEGQI_CEX";
    case InferenceId::QUANTIFIERS_CEGQI_CEX_AUX:
      return "QUANTIFIERS_CEGQI_CEX_AUX";
    case InferenceId::QUANTIFIERS_CEGQI_NESTED_QE:
      return "QUANTIFIERS_CEGQI_NESTED_QE";
    case InferenceId::QUANTIFIERS_CEGQI_CEX_DEP:
      return "QUANTIFIERS_CEGQI_CEX_DEP";
    case InferenceId::QUANTIFIERS_CEGQI_VTS_LB_DELTA:
      return "QUANTIFIERS_CEGQI_VTS_LB_DELTA";
    case InferenceId::QUANTIFIERS_CEGQI_VTS_UB_DELTA:
      return "QUANTIFIERS_CEGQI_VTS_UB_DELTA";
    case InferenceId::QUANTIFIERS_CEGQI_VTS_LB_INF:
      return "QUANTIFIERS_CEGQI_VTS_LB_INF";
    case InferenceId::QUANTIFIERS_SYQI_CEX: return "QUANTIFIERS_SYQI_CEX";
    case InferenceId::QUANTIFIERS_SYQI_EVAL_UNFOLD:
      return "QUANTIFIERS_SYQI_EVAL_UNFOLD";
    case InferenceId::QUANTIFIERS_SYGUS_QE_PREPROC:
      return "QUANTIFIERS_SYGUS_QE_PREPROC";
    case InferenceId::QUANTIFIERS_SYGUS_ENUM_ACTIVE_GUARD_SPLIT:
      return "QUANTIFIERS_SYGUS_ENUM_ACTIVE_GUARD_SPLIT";
    case InferenceId::QUANTIFIERS_SYGUS_EXCLUDE_CURRENT:
      return "QUANTIFIERS_SYGUS_EXCLUDE_CURRENT";
    case InferenceId::QUANTIFIERS_SYGUS_STREAM_EXCLUDE_CURRENT:
      return "QUANTIFIERS_SYGUS_STREAM_EXCLUDE_CURRENT";
    case InferenceId::QUANTIFIERS_SYGUS_EXAMPLE_INFER_CONTRA:
      return "QUANTIFIERS_SYGUS_EXAMPLE_INFER_CONTRA";
    case InferenceId::QUANTIFIERS_DSPLIT: return "QUANTIFIERS_DSPLIT";
    case InferenceId::QUANTIFIERS_SKOLEMIZE: return "QUANTIFIERS_SKOLEMIZE";
    case InferenceId::QUANTIFIERS_REDUCE_ALPHA_EQ:
      return "QUANTIFIERS_REDUCE_ALPHA_EQ";
    case InferenceId::QUANTIFIERS_HO_MATCH_PRED:
      return "QUANTIFIERS_HO_MATCH_PRED";
    case InferenceId::QUANTIFIERS_PARTIAL_TRIGGER_REDUCE:
      return "QUANTIFIERS_PARTIAL_TRIGGER_REDUCE";

    case InferenceId::SEP_PTO_NEG_PROP: return "SEP_PTO_NEG_PROP";
    case InferenceId::SEP_PTO_PROP: return "SEP_PTO_PROP";
    case InferenceId::SEP_LABEL_INTRO: return "SEP_LABEL_INTRO";
    case InferenceId::SEP_LABEL_DEF: return "SEP_LABEL_DEF";
    case InferenceId::SEP_EMP: return "SEP_EMP";
    case InferenceId::SEP_POS_REDUCTION: return "SEP_POS_REDUCTION";
    case InferenceId::SEP_NEG_REDUCTION: return "SEP_NEG_REDUCTION";
    case InferenceId::SEP_REFINEMENT: return "SEP_REFINEMENT";
    case InferenceId::SEP_NIL_NOT_IN_HEAP: return "SEP_NIL_NOT_IN_HEAP";
    case InferenceId::SEP_SYM_BREAK: return "SEP_SYM_BREAK";
    case InferenceId::SEP_WITNESS_FINITE_DATA: return "SEP_WITNESS_FINITE_DATA";
    case InferenceId::SEP_DISTINCT_REF: return "SEP_DISTINCT_REF";
    case InferenceId::SEP_REF_BOUND: return "SEP_REF_BOUND";

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
    case InferenceId::SETS_CARD_SPLIT_EMPTY: return "SETS_CARD_SPLIT_EMPTY";
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

    case InferenceId::STRINGS_I_NORM_S: return "STRINGS_I_NORM_S";
    case InferenceId::STRINGS_I_CONST_MERGE: return "STRINGS_I_CONST_MERGE";
    case InferenceId::STRINGS_I_CONST_CONFLICT:
      return "STRINGS_I_CONST_CONFLICT";
    case InferenceId::STRINGS_I_NORM: return "STRINGS_I_NORM";
    case InferenceId::STRINGS_UNIT_INJ: return "STRINGS_UNIT_INJ";
    case InferenceId::STRINGS_UNIT_CONST_CONFLICT:
      return "STRINGS_UNIT_CONST_CONFLICT";
    case InferenceId::STRINGS_UNIT_INJ_DEQ: return "STRINGS_UNIT_INJ_DEQ";
    case InferenceId::STRINGS_CARD_SP: return "STRINGS_CARD_SP";
    case InferenceId::STRINGS_CARDINALITY: return "STRINGS_CARDINALITY";
    case InferenceId::STRINGS_I_CYCLE_E: return "STRINGS_I_CYCLE_E";
    case InferenceId::STRINGS_I_CYCLE: return "STRINGS_I_CYCLE";
    case InferenceId::STRINGS_F_CONST: return "STRINGS_F_CONST";
    case InferenceId::STRINGS_F_UNIFY: return "STRINGS_F_UNIFY";
    case InferenceId::STRINGS_F_ENDPOINT_EMP: return "STRINGS_F_ENDPOINT_EMP";
    case InferenceId::STRINGS_F_ENDPOINT_EQ: return "STRINGS_F_ENDPOINT_EQ";
    case InferenceId::STRINGS_F_NCTN: return "STRINGS_F_NCTN";
    case InferenceId::STRINGS_N_EQ_CONF: return "STRINGS_N_EQ_CONF";
    case InferenceId::STRINGS_N_ENDPOINT_EMP: return "STRINGS_N_ENDPOINT_EMP";
    case InferenceId::STRINGS_N_UNIFY: return "STRINGS_N_UNIFY";
    case InferenceId::STRINGS_N_ENDPOINT_EQ: return "STRINGS_N_ENDPOINT_EQ";
    case InferenceId::STRINGS_N_CONST: return "STRINGS_N_CONST";
    case InferenceId::STRINGS_INFER_EMP: return "STRINGS_INFER_EMP";
    case InferenceId::STRINGS_SSPLIT_CST_PROP: return "STRINGS_SSPLIT_CST_PROP";
    case InferenceId::STRINGS_SSPLIT_VAR_PROP: return "STRINGS_SSPLIT_VAR_PROP";
    case InferenceId::STRINGS_LEN_SPLIT: return "STRINGS_LEN_SPLIT";
    case InferenceId::STRINGS_LEN_SPLIT_EMP: return "STRINGS_LEN_SPLIT_EMP";
    case InferenceId::STRINGS_SSPLIT_CST: return "STRINGS_SSPLIT_CST";
    case InferenceId::STRINGS_SSPLIT_VAR: return "STRINGS_SSPLIT_VAR";
    case InferenceId::STRINGS_FLOOP: return "STRINGS_FLOOP";
    case InferenceId::STRINGS_FLOOP_CONFLICT: return "STRINGS_FLOOP_CONFLICT";
    case InferenceId::STRINGS_NORMAL_FORM: return "STRINGS_NORMAL_FORM";
    case InferenceId::STRINGS_N_NCTN: return "STRINGS_N_NCTN";
    case InferenceId::STRINGS_LEN_NORM: return "STRINGS_LEN_NORM";
    case InferenceId::STRINGS_DEQ_DISL_EMP_SPLIT:
      return "STRINGS_DEQ_DISL_EMP_SPLIT";
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
      return "STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT";
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
      return "STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT";
    case InferenceId::STRINGS_DEQ_STRINGS_EQ: return "STRINGS_DEQ_STRINGS_EQ";
    case InferenceId::STRINGS_DEQ_DISL_STRINGS_SPLIT:
      return "STRINGS_DEQ_DISL_STRINGS_SPLIT";
    case InferenceId::STRINGS_DEQ_LENS_EQ: return "STRINGS_DEQ_LENS_EQ";
    case InferenceId::STRINGS_DEQ_NORM_EMP: return "STRINGS_DEQ_NORM_EMP";
    case InferenceId::STRINGS_DEQ_LENGTH_SP: return "STRINGS_DEQ_LENGTH_SP";
    case InferenceId::STRINGS_CODE_PROXY: return "STRINGS_CODE_PROXY";
    case InferenceId::STRINGS_CODE_INJ: return "STRINGS_CODE_INJ";
    case InferenceId::STRINGS_RE_NF_CONFLICT: return "STRINGS_RE_NF_CONFLICT";
    case InferenceId::STRINGS_RE_UNFOLD_POS: return "STRINGS_RE_UNFOLD_POS";
    case InferenceId::STRINGS_RE_UNFOLD_NEG: return "STRINGS_RE_UNFOLD_NEG";
    case InferenceId::STRINGS_RE_INTER_INCLUDE:
      return "STRINGS_RE_INTER_INCLUDE";
    case InferenceId::STRINGS_RE_INTER_CONF: return "STRINGS_RE_INTER_CONF";
    case InferenceId::STRINGS_RE_INTER_INFER: return "STRINGS_RE_INTER_INFER";
    case InferenceId::STRINGS_RE_DELTA: return "STRINGS_RE_DELTA";
    case InferenceId::STRINGS_RE_DELTA_CONF: return "STRINGS_RE_DELTA_CONF";
    case InferenceId::STRINGS_RE_DERIVE: return "STRINGS_RE_DERIVE";
    case InferenceId::STRINGS_EXTF: return "STRINGS_EXTF";
    case InferenceId::STRINGS_EXTF_N: return "STRINGS_EXTF_N";
    case InferenceId::STRINGS_EXTF_D: return "STRINGS_EXTF_D";
    case InferenceId::STRINGS_EXTF_D_N: return "STRINGS_EXTF_D_N";
    case InferenceId::STRINGS_EXTF_EQ_REW: return "STRINGS_EXTF_EQ_REW";
    case InferenceId::STRINGS_CTN_TRANS: return "STRINGS_CTN_TRANS";
    case InferenceId::STRINGS_CTN_DECOMPOSE: return "STRINGS_CTN_DECOMPOSE";
    case InferenceId::STRINGS_CTN_NEG_EQUAL: return "STRINGS_CTN_NEG_EQUAL";
    case InferenceId::STRINGS_CTN_POS: return "STRINGS_CTN_POS";
    case InferenceId::STRINGS_REDUCTION: return "STRINGS_REDUCTION";
    case InferenceId::STRINGS_PREFIX_CONFLICT: return "STRINGS_PREFIX_CONFLICT";
    case InferenceId::STRINGS_REGISTER_TERM_ATOMIC:
      return "STRINGS_REGISTER_TERM_ATOMIC";
    case InferenceId::STRINGS_REGISTER_TERM: return "STRINGS_REGISTER_TERM";
    case InferenceId::STRINGS_CMI_SPLIT: return "STRINGS_CMI_SPLIT";

    case InferenceId::UF_BREAK_SYMMETRY: return "UF_BREAK_SYMMETRY";
    case InferenceId::UF_CARD_CLIQUE: return "UF_CARD_CLIQUE";
    case InferenceId::UF_CARD_COMBINED: return "UF_CARD_COMBINED";
    case InferenceId::UF_CARD_ENFORCE_NEGATIVE: return "UF_CARD_ENFORCE_NEGATIVE";
    case InferenceId::UF_CARD_EQUIV: return "UF_CARD_EQUIV";
    case InferenceId::UF_CARD_MONOTONE_COMBINED: return "UF_CARD_MONOTONE_COMBINED";
    case InferenceId::UF_CARD_SIMPLE_CONFLICT: return "UF_CARD_SIMPLE_CONFLICT";
    case InferenceId::UF_CARD_SPLIT: return "UF_CARD_SPLIT";

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
}  // namespace cvc5
