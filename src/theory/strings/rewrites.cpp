/*********************                                                        */
/*! \file rewrites.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference information utility.
 **/

#include "theory/strings/rewrites.h"

#include <iostream>

namespace CVC4 {
namespace theory {
namespace strings {

const char* toString(Rewrite r)
{
  switch (r)
  {
    case Rewrite::CTN_COMPONENT: return "CTN_COMPONENT";
    case Rewrite::CTN_CONCAT_CHAR: return "CTN_CONCAT_CHAR";
    case Rewrite::CTN_CONST: return "CTN_CONST";
    case Rewrite::CTN_EQ: return "CTN_EQ";
    case Rewrite::CTN_LEN_INEQ: return "CTN_LEN_INEQ";
    case Rewrite::CTN_LEN_INEQ_NSTRICT: return "CTN_LEN_INEQ_NSTRICT";
    case Rewrite::CTN_LHS_EMPTYSTR: return "CTN_LHS_EMPTYSTR";
    case Rewrite::CTN_MSET_NSS: return "CTN_MSET_NSS";
    case Rewrite::CTN_NCONST_CTN_CONCAT: return "CTN_NCONST_CTN_CONCAT";
    case Rewrite::CTN_REPL: return "CTN_REPL";
    case Rewrite::CTN_REPL_CHAR: return "CTN_REPL_CHAR";
    case Rewrite::CTN_REPL_CNSTS_TO_CTN: return "CTN_REPL_CNSTS_TO_CTN";
    case Rewrite::CTN_REPL_EMPTY: return "CTN_REPL_EMPTY";
    case Rewrite::CTN_REPL_LEN_ONE_TO_CTN: return "CTN_REPL_LEN_ONE_TO_CTN";
    case Rewrite::CTN_REPL_SELF: return "CTN_REPL_SELF";
    case Rewrite::CTN_REPL_SIMP_REPL: return "CTN_REPL_SIMP_REPL";
    case Rewrite::CTN_REPL_TO_CTN: return "CTN_REPL_TO_CTN";
    case Rewrite::CTN_REPL_TO_CTN_DISJ: return "CTN_REPL_TO_CTN_DISJ";
    case Rewrite::CTN_RHS_EMPTYSTR: return "CTN_RHS_EMPTYSTR";
    case Rewrite::CTN_RPL_NON_CTN: return "CTN_RPL_NON_CTN";
    case Rewrite::CTN_SPLIT: return "CTN_SPLIT";
    case Rewrite::CTN_SPLIT_ONES: return "CTN_SPLIT_ONES";
    case Rewrite::CTN_STRIP_ENDPT: return "CTN_STRIP_ENDPT";
    case Rewrite::CTN_SUBSTR: return "CTN_SUBSTR";
    case Rewrite::EQ_LEN_DEQ: return "EQ_LEN_DEQ";
    case Rewrite::EQ_NCTN: return "EQ_NCTN";
    case Rewrite::EQ_NFIX: return "EQ_NFIX";
    case Rewrite::FROM_CODE_EVAL: return "FROM_CODE_EVAL";
    case Rewrite::IDOF_DEF_CTN: return "IDOF_DEF_CTN";
    case Rewrite::IDOF_EMP_IDOF: return "IDOF_EMP_IDOF";
    case Rewrite::IDOF_EQ_CST_START: return "IDOF_EQ_CST_START";
    case Rewrite::IDOF_EQ_NORM: return "IDOF_EQ_NORM";
    case Rewrite::IDOF_EQ_NSTART: return "IDOF_EQ_NSTART";
    case Rewrite::IDOF_FIND: return "IDOF_FIND";
    case Rewrite::IDOF_LEN: return "IDOF_LEN";
    case Rewrite::IDOF_MAX: return "IDOF_MAX";
    case Rewrite::IDOF_NCTN: return "IDOF_NCTN";
    case Rewrite::IDOF_NEG: return "IDOF_NEG";
    case Rewrite::IDOF_NFIND: return "IDOF_NFIND";
    case Rewrite::IDOF_NORM_PREFIX: return "IDOF_NORM_PREFIX";
    case Rewrite::IDOF_PULL_ENDPT: return "IDOF_PULL_ENDPT";
    case Rewrite::IDOF_STRIP_CNST_ENDPTS: return "IDOF_STRIP_CNST_ENDPTS";
    case Rewrite::IDOF_STRIP_SYM_LEN: return "IDOF_STRIP_SYM_LEN";
    case Rewrite::ITOS_EVAL: return "ITOS_EVAL";
    case Rewrite::RE_AND_EMPTY: return "RE_AND_EMPTY";
    case Rewrite::RE_ANDOR_FLATTEN: return "RE_ANDOR_FLATTEN";
    case Rewrite::RE_CHAR_IN_STR_STAR: return "RE_CHAR_IN_STR_STAR";
    case Rewrite::RE_CONCAT: return "RE_CONCAT";
    case Rewrite::RE_CONCAT_FLATTEN: return "RE_CONCAT_FLATTEN";
    case Rewrite::RE_CONCAT_OPT: return "RE_CONCAT_OPT";
    case Rewrite::RE_CONCAT_PURE_ALLCHAR: return "RE_CONCAT_PURE_ALLCHAR";
    case Rewrite::RE_CONCAT_TO_CONTAINS: return "RE_CONCAT_TO_CONTAINS";
    case Rewrite::RE_EMPTY_IN_STR_STAR: return "RE_EMPTY_IN_STR_STAR";
    case Rewrite::RE_IN_DIST_CHAR_STAR: return "RE_IN_DIST_CHAR_STAR";
    case Rewrite::RE_IN_SIGMA_STAR: return "RE_IN_SIGMA_STAR";
    case Rewrite::RE_LOOP: return "RE_LOOP";
    case Rewrite::RE_LOOP_STAR: return "RE_LOOP_STAR";
    case Rewrite::RE_OR_ALL: return "RE_OR_ALL";
    case Rewrite::RE_SIMPLE_CONSUME: return "RE_SIMPLE_CONSUME";
    case Rewrite::RE_STAR_EMPTY: return "RE_STAR_EMPTY";
    case Rewrite::RE_STAR_EMPTY_STRING: return "RE_STAR_EMPTY_STRING";
    case Rewrite::RE_STAR_NESTED_STAR: return "RE_STAR_NESTED_STAR";
    case Rewrite::RE_STAR_UNION: return "RE_STAR_UNION";
    case Rewrite::REPL_CHAR_NCONTRIB_FIND: return "REPL_CHAR_NCONTRIB_FIND";
    case Rewrite::REPL_DUAL_REPL_ITE: return "REPL_DUAL_REPL_ITE";
    case Rewrite::REPL_REPL_SHORT_CIRCUIT: return "REPL_REPL_SHORT_CIRCUIT";
    case Rewrite::REPL_REPL2_INV: return "REPL_REPL2_INV";
    case Rewrite::REPL_REPL2_INV_ID: return "REPL_REPL2_INV_ID";
    case Rewrite::REPL_REPL3_INV: return "REPL_REPL3_INV";
    case Rewrite::REPL_REPL3_INV_ID: return "REPL_REPL3_INV_ID";
    case Rewrite::REPL_SUBST_IDX: return "REPL_SUBST_IDX";
    case Rewrite::REPLALL_CONST: return "REPLALL_CONST";
    case Rewrite::REPLALL_EMPTY_FIND: return "REPLALL_EMPTY_FIND";
    case Rewrite::RPL_CCTN: return "RPL_CCTN";
    case Rewrite::RPL_CCTN_RPL: return "RPL_CCTN_RPL";
    case Rewrite::RPL_CNTS_SUBSTS: return "RPL_CNTS_SUBSTS";
    case Rewrite::RPL_CONST_FIND: return "RPL_CONST_FIND";
    case Rewrite::RPL_CONST_NFIND: return "RPL_CONST_NFIND";
    case Rewrite::RPL_EMP_CNTS_SUBSTS: return "RPL_EMP_CNTS_SUBSTS";
    case Rewrite::RPL_ID: return "RPL_ID";
    case Rewrite::RPL_NCTN: return "RPL_NCTN";
    case Rewrite::RPL_PULL_ENDPT: return "RPL_PULL_ENDPT";
    case Rewrite::RPL_REPLACE: return "RPL_REPLACE";
    case Rewrite::RPL_RPL_EMPTY: return "RPL_RPL_EMPTY";
    case Rewrite::RPL_RPL_LEN_ID: return "RPL_RPL_LEN_ID";
    case Rewrite::RPL_X_Y_X_SIMP: return "RPL_X_Y_X_SIMP";
    case Rewrite::SPLIT_EQ: return "SPLIT_EQ";
    case Rewrite::SPLIT_EQ_STRIP_L: return "SPLIT_EQ_STRIP_L";
    case Rewrite::SPLIT_EQ_STRIP_R: return "SPLIT_EQ_STRIP_R";
    case Rewrite::SS_COMBINE: return "SS_COMBINE";
    case Rewrite::SS_CONST_END_OOB: return "SS_CONST_END_OOB";
    case Rewrite::SS_CONST_LEN_MAX_OOB: return "SS_CONST_LEN_MAX_OOB";
    case Rewrite::SS_CONST_LEN_NON_POS: return "SS_CONST_LEN_NON_POS";
    case Rewrite::SS_CONST_SS: return "SS_CONST_SS";
    case Rewrite::SS_CONST_START_MAX_OOB: return "SS_CONST_START_MAX_OOB";
    case Rewrite::SS_CONST_START_NEG: return "SS_CONST_START_NEG";
    case Rewrite::SS_CONST_START_OOB: return "SS_CONST_START_OOB";
    case Rewrite::SS_EMPTYSTR: return "SS_EMPTYSTR";
    case Rewrite::SS_END_PT_NORM: return "SS_END_PT_NORM";
    case Rewrite::SS_GEQ_ZERO_START_ENTAILS_EMP_S:
      return "SS_GEQ_ZERO_START_ENTAILS_EMP_S";
    case Rewrite::SS_LEN_INCLUDE: return "SS_LEN_INCLUDE";
    case Rewrite::SS_LEN_NON_POS: return "SS_LEN_NON_POS";
    case Rewrite::SS_LEN_ONE_Z_Z: return "SS_LEN_ONE_Z_Z";
    case Rewrite::SS_NON_ZERO_LEN_ENTAILS_OOB:
      return "SS_NON_ZERO_LEN_ENTAILS_OOB";
    case Rewrite::SS_START_ENTAILS_ZERO_LEN: return "SS_START_ENTAILS_ZERO_LEN";
    case Rewrite::SS_START_GEQ_LEN: return "SS_START_GEQ_LEN";
    case Rewrite::SS_START_NEG: return "SS_START_NEG";
    case Rewrite::SS_STRIP_END_PT: return "SS_STRIP_END_PT";
    case Rewrite::SS_STRIP_START_PT: return "SS_STRIP_START_PT";
    case Rewrite::STOI_CONCAT_NONNUM: return "STOI_CONCAT_NONNUM";
    case Rewrite::STOI_EVAL: return "STOI_EVAL";
    case Rewrite::STR_CONV_CONST: return "STR_CONV_CONST";
    case Rewrite::STR_CONV_IDEM: return "STR_CONV_IDEM";
    case Rewrite::STR_CONV_ITOS: return "STR_CONV_ITOS";
    case Rewrite::STR_CONV_MINSCOPE_CONCAT: return "STR_CONV_MINSCOPE_CONCAT";
    case Rewrite::STR_EMP_REPL_EMP: return "STR_EMP_REPL_EMP";
    case Rewrite::STR_EMP_REPL_EMP_R: return "STR_EMP_REPL_EMP_R";
    case Rewrite::STR_EMP_REPL_X_Y_X: return "STR_EMP_REPL_X_Y_X";
    case Rewrite::STR_EMP_SUBSTR_ELIM: return "STR_EMP_SUBSTR_ELIM";
    case Rewrite::STR_EMP_SUBSTR_LEQ_LEN: return "STR_EMP_SUBSTR_LEQ_LEN";
    case Rewrite::STR_EMP_SUBSTR_LEQ_Z: return "STR_EMP_SUBSTR_LEQ_Z";
    case Rewrite::STR_EQ_CONJ_LEN_ENTAIL: return "STR_EQ_CONJ_LEN_ENTAIL";
    case Rewrite::STR_EQ_CONST_NHOMOG: return "STR_EQ_CONST_NHOMOG";
    case Rewrite::STR_EQ_HOMOG_CONST: return "STR_EQ_HOMOG_CONST";
    case Rewrite::STR_EQ_REPL_EMP: return "STR_EQ_REPL_EMP";
    case Rewrite::STR_EQ_REPL_NOT_CTN: return "STR_EQ_REPL_NOT_CTN";
    case Rewrite::STR_EQ_REPL_TO_DIS: return "STR_EQ_REPL_TO_DIS";
    case Rewrite::STR_EQ_REPL_TO_EQ: return "STR_EQ_REPL_TO_EQ";
    case Rewrite::STR_EQ_UNIFY: return "STR_EQ_UNIFY";
    case Rewrite::STR_LEQ_CPREFIX: return "STR_LEQ_CPREFIX";
    case Rewrite::STR_LEQ_EMPTY: return "STR_LEQ_EMPTY";
    case Rewrite::STR_LEQ_EVAL: return "STR_LEQ_EVAL";
    case Rewrite::STR_LEQ_ID: return "STR_LEQ_ID";
    case Rewrite::STR_REV_CONST: return "STR_REV_CONST";
    case Rewrite::STR_REV_IDEM: return "STR_REV_IDEM";
    case Rewrite::STR_REV_MINSCOPE_CONCAT: return "STR_REV_MINSCOPE_CONCAT";
    case Rewrite::SUBSTR_REPL_SWAP: return "SUBSTR_REPL_SWAP";
    case Rewrite::SUF_PREFIX_CONST: return "SUF_PREFIX_CONST";
    case Rewrite::SUF_PREFIX_CTN: return "SUF_PREFIX_CTN";
    case Rewrite::SUF_PREFIX_EMPTY: return "SUF_PREFIX_EMPTY";
    case Rewrite::SUF_PREFIX_EMPTY_CONST: return "SUF_PREFIX_EMPTY_CONST";
    case Rewrite::SUF_PREFIX_EQ: return "SUF_PREFIX_EQ";
    case Rewrite::SUF_PREFIX_TO_EQS: return "SUF_PREFIX_TO_EQS";
    case Rewrite::TO_CODE_EVAL: return "TO_CODE_EVAL";
    case Rewrite::EQ_REFL: return "EQ_REFL";
    case Rewrite::EQ_CONST_FALSE: return "EQ_CONST_FALSE";
    case Rewrite::EQ_SYM: return "EQ_SYM";
    case Rewrite::CONCAT_NORM: return "CONCAT_NORM";
    case Rewrite::IS_DIGIT_ELIM: return "IS_DIGIT_ELIM";
    case Rewrite::RE_CONCAT_EMPTY: return "RE_CONCAT_EMPTY";
    case Rewrite::RE_CONSUME_CCONF: return "RE_CONSUME_CCONF";
    case Rewrite::RE_CONSUME_S: return "RE_CONSUME_S";
    case Rewrite::RE_CONSUME_S_CCONF: return "RE_CONSUME_S_CCONF";
    case Rewrite::RE_CONSUME_S_FULL: return "RE_CONSUME_S_FULL";
    case Rewrite::RE_IN_EMPTY: return "RE_IN_EMPTY";
    case Rewrite::RE_IN_SIGMA: return "RE_IN_SIGMA";
    case Rewrite::RE_IN_EVAL: return "RE_IN_EVAL";
    case Rewrite::RE_IN_COMPLEMENT: return "RE_IN_COMPLEMENT";
    case Rewrite::RE_IN_RANGE: return "RE_IN_RANGE";
    case Rewrite::RE_IN_CSTRING: return "RE_IN_CSTRING";
    case Rewrite::RE_IN_ANDOR: return "RE_IN_ANDOR";
    case Rewrite::RE_REPEAT_ELIM: return "RE_REPEAT_ELIM";
    case Rewrite::SUF_PREFIX_ELIM: return "SUF_PREFIX_ELIM";
    case Rewrite::STR_LT_ELIM: return "STR_LT_ELIM";
    case Rewrite::RE_RANGE_SINGLE: return "RE_RANGE_SINGLE";
    case Rewrite::RE_OPT_ELIM: return "RE_OPT_ELIM";
    case Rewrite::RE_PLUS_ELIM: return "RE_PLUS_ELIM";
    case Rewrite::RE_DIFF_ELIM: return "RE_DIFF_ELIM";
    case Rewrite::LEN_EVAL: return "LEN_EVAL";
    case Rewrite::LEN_CONCAT: return "LEN_CONCAT";
    case Rewrite::LEN_REPL_INV: return "LEN_REPL_INV";
    case Rewrite::LEN_CONV_INV: return "LEN_CONV_INV";
    case Rewrite::CHARAT_ELIM: return "CHARAT_ELIM";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Rewrite r)
{
  out << toString(r);
  return out;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
