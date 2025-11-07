/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of trust identifier
 */

#include "proof/trust_id.h"

#include "proof/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

const char* toString(TrustId id)
{
  switch (id)
  {
    case TrustId::NONE: return "NONE";
    case TrustId::PREPROCESSED_INPUT: return "PREPROCESSED_INPUT";
    case TrustId::THEORY_LEMMA: return "THEORY_LEMMA";
    case TrustId::SMT_REFUTATION: return "SMT_REFUTATION";
    // core
    case TrustId::THEORY_INFERENCE_ARITH: return "THEORY_INFERENCE_ARITH";
    case TrustId::THEORY_INFERENCE_ARRAYS: return "THEORY_INFERENCE_ARRAYS";
    case TrustId::THEORY_INFERENCE_DATATYPES:
      return "THEORY_INFERENCE_DATATYPES";
    case TrustId::THEORY_INFERENCE_SEP: return "THEORY_INFERENCE_SEP";
    case TrustId::THEORY_INFERENCE_SETS: return "THEORY_INFERENCE_SETS";
    case TrustId::THEORY_INFERENCE_STRINGS: return "THEORY_INFERENCE_STRINGS";
    case TrustId::PP_STATIC_REWRITE: return "PP_STATIC_REWRITE";
    case TrustId::THEORY_PREPROCESS: return "THEORY_PREPROCESS";
    case TrustId::THEORY_PREPROCESS_LEMMA: return "THEORY_PREPROCESS_LEMMA";
    case TrustId::THEORY_EXPAND_DEF: return "THEORY_EXPAND_DEF";
    // preprocess passes
    case TrustId::PREPROCESS_BV_GUASS: return "PREPROCESS_BV_GUASS";
    case TrustId::PREPROCESS_BV_GUASS_LEMMA: return "PREPROCESS_BV_GUASS_LEMMA";
    case TrustId::PREPROCESS_BV_TO_BOOL: return "PREPROCESS_BV_TO_BOOL";
    case TrustId::PREPROCESS_BV_TO_INT: return "PREPROCESS_BV_TO_INT";
    case TrustId::PREPROCESS_BV_TO_INT_LEMMA:
      return "PREPROCESS_BV_TO_INT_LEMMA";
    case TrustId::PREPROCESS_BOOL_TO_BV: return "PREPROCESS_BOOL_TO_BV";
    case TrustId::PREPROCESS_ACKERMANN: return "PREPROCESS_ACKERMANN";
    case TrustId::PREPROCESS_ACKERMANN_LEMMA:
      return "PREPROCESS_ACKERMANN_LEMMA";
    case TrustId::PREPROCESS_STATIC_LEARNING_LEMMA:
      return "PREPROCESS_STATIC_LEARNING_LEMMA";
    case TrustId::PREPROCESS_HO_ELIM: return "PREPROCESS_HO_ELIM";
    case TrustId::PREPROCESS_HO_ELIM_LEMMA: return "PREPROCESS_HO_ELIM_LEMMA";
    case TrustId::PREPROCESS_BITVECTOR_EAGER_ATOMS:
      return "PREPROCESS_BITVECTOR_EAGER_ATOMS";
    case TrustId::PREPROCESS_FF_BITSUM: return "PREPROCESS_FF_BITSUM";
    case TrustId::PREPROCESS_FF_DISJUNCTIVE_BIT:
      return "PREPROCESS_FF_DISJUNCTIVE_BIT";
    case TrustId::PREPROCESS_FUN_DEF_FMF: return "PREPROCESS_FUN_DEF_FMF";
    case TrustId::PREPROCESS_ITE_SIMP: return "PREPROCESS_ITE_SIMP";
    case TrustId::PREPROCESS_LEARNED_REWRITE:
      return "PREPROCESS_LEARNED_REWRITE";
    case TrustId::PREPROCESS_LEARNED_REWRITE_LEMMA:
      return "PREPROCESS_LEARNED_REWRITE_LEMMA";
    case TrustId::PREPROCESS_MIPLIB_TRICK: return "PREPROCESS_MIPLIB_TRICK";
    case TrustId::PREPROCESS_MIPLIB_TRICK_LEMMA:
      return "PREPROCESS_MIPLIB_TRICK_LEMMA";
    case TrustId::PREPROCESS_NL_EXT_PURIFY: return "PREPROCESS_NL_EXT_PURIFY";
    case TrustId::PREPROCESS_NL_EXT_PURIFY_LEMMA:
      return "PREPROCESS_NL_EXT_PURIFY_LEMMA";
    case TrustId::PREPROCESS_BV_INTRO_POW2: return "PREPROCESS_BV_INTRO_POW2";
    case TrustId::PREPROCESS_FOREIGN_THEORY_REWRITE:
      return "PREPROCESS_FOREIGN_THEORY_REWRITE";
    case TrustId::PREPROCESS_UNCONSTRAINED_SIMP:
      return "PREPROCESS_UNCONSTRAINED_SIMP";
    case TrustId::PREPROCESS_QUANTIFIERS_PP: return "PREPROCESS_QUANTIFIERS_PP";
    case TrustId::PREPROCESS_REAL_TO_INT: return "PREPROCESS_REAL_TO_INT";
    case TrustId::PREPROCESS_SORT_INFER: return "PREPROCESS_SORT_INFER";
    case TrustId::PREPROCESS_SORT_INFER_LEMMA:
      return "PREPROCESS_SORT_INFER_LEMMA";
    case TrustId::PREPROCESS_STRINGS_EAGER_PP:
      return "PREPROCESS_STRINGS_EAGER_PP";
    // other
    case TrustId::UF_DISTINCT: return "UF_DISTINCT";
    case TrustId::ARITH_NL_COVERING_DIRECT: return "ARITH_NL_COVERING_DIRECT";
    case TrustId::ARITH_NL_COVERING_RECURSIVE:
      return "ARITH_NL_COVERING_RECURSIVE";
    case TrustId::ARITH_NL_COMPARE_LIT_TRANSFORM:
      return "ARITH_NL_COMPARE_LIT_TRANSFORM";
    case TrustId::ARITH_DIO_LEMMA: return "ARITH_DIO_LEMMA";
    case TrustId::ARITH_STATIC_LEARN: return "ARITH_STATIC_LEARN";
    case TrustId::ARITH_NL_COMPARE_LEMMA: return "ARITH_NL_COMPARE_LEMMA";
    case TrustId::ARITH_NL_FLATTEN_MON_LEMMA:
      return "ARITH_NL_FLATTEN_MON_LEMMA";
    case TrustId::BV_BITBLAST_CONFLICT: return "BV_BITBLAST_CONFLICT";
    case TrustId::BV_PP_ASSERT: return "BV_PP_ASSERT";
    case TrustId::DIAMONDS: return "DIAMONDS";
    case TrustId::EXT_THEORY_REWRITE: return "EXT_THEORY_REWRITE";
    case TrustId::REWRITE_NO_ELABORATE: return "REWRITE_NO_ELABORATE";
    case TrustId::FLATTENING_REWRITE: return "FLATTENING_REWRITE";
    case TrustId::SUBS_NO_ELABORATE: return "SUBS_NO_ELABORATE";
    case TrustId::SUBS_MAP: return "SUBS_MAP";
    case TrustId::SUBS_EQ: return "SUBS_EQ";
    case TrustId::ARITH_PRED_CAST_TYPE: return "ARITH_PRED_CAST_TYPE";
    case TrustId::RE_ELIM: return "RE_ELIM";
    case TrustId::QUANTIFIERS_PREPROCESS: return "QUANTIFIERS_PREPROCESS";
    case TrustId::QUANTIFIERS_INST_REWRITE: return "QUANTIFIERS_INST_REWRITE";
    case TrustId::QUANTIFIERS_SUB_CBQI_LEMMA:
      return "QUANTIFIERS_SUB_CBQI_LEMMA";
    case TrustId::QUANTIFIERS_NESTED_QE_LEMMA:
      return "QUANTIFIERS_NESTED_QE_LEMMA";
    case TrustId::STRINGS_PP_STATIC_REWRITE: return "STRINGS_PP_STATIC_REWRITE";
    case TrustId::VALID_WITNESS: return "VALID_WITNESS";
    case TrustId::SUBTYPE_ELIMINATION: return "SUBTYPE_ELIMINATION";
    case TrustId::MACRO_THEORY_REWRITE_RCONS:
      return "MACRO_THEORY_REWRITE_RCONS";
    case TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE:
      return "MACRO_THEORY_REWRITE_RCONS_SIMPLE";
    case TrustId::INT_BLASTER: return "INT_BLASTER";
    // unknown sources
    case TrustId::UNKNOWN_PREPROCESS: return "UNKNOWN_PREPROCESS";
    case TrustId::UNKNOWN_PREPROCESS_LEMMA: return "UNKNOWN_PREPROCESS_LEMMA";
    default: return "TrustId::Unknown";
  };
}

std::ostream& operator<<(std::ostream& out, TrustId id)
{
  out << toString(id);
  return out;
}

Node mkTrustId(NodeManager* nm, TrustId id)
{
  return nm->mkConstInt(Rational(static_cast<uint32_t>(id)));
}

bool getTrustId(TNode n, TrustId& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<TrustId>(index);
  return true;
}

}  // namespace cvc5::internal
