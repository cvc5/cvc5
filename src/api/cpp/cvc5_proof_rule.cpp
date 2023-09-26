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

#include "proof/proof_rule.h"

#include <iostream>

namespace cvc5::internal {

const char* toString(PfRule id)
{
  switch (id)
  {
    //================================================= Core rules
    case PfRule::ASSUME: return "ASSUME";
    case PfRule::SCOPE: return "SCOPE";
    case PfRule::SUBS: return "SUBS";
    case PfRule::REWRITE: return "REWRITE";
    case PfRule::EVALUATE: return "EVALUATE";
    case PfRule::MACRO_SR_EQ_INTRO: return "MACRO_SR_EQ_INTRO";
    case PfRule::MACRO_SR_PRED_INTRO: return "MACRO_SR_PRED_INTRO";
    case PfRule::MACRO_SR_PRED_ELIM: return "MACRO_SR_PRED_ELIM";
    case PfRule::MACRO_SR_PRED_TRANSFORM: return "MACRO_SR_PRED_TRANSFORM";
    case PfRule::ENCODE_PRED_TRANSFORM: return "ENCODE_PRED_TRANSFORM";
    case PfRule::ANNOTATION: return "ANNOTATION";
    case PfRule::DSL_REWRITE: return "DSL_REWRITE";
    case PfRule::REMOVE_TERM_FORMULA_AXIOM: return "REMOVE_TERM_FORMULA_AXIOM";
    //================================================= Trusted rules
    case PfRule::THEORY_LEMMA: return "THEORY_LEMMA";
    case PfRule::THEORY_REWRITE: return "THEORY_REWRITE";
    case PfRule::PREPROCESS: return "PREPROCESS";
    case PfRule::PREPROCESS_LEMMA: return "PREPROCESS_LEMMA";
    case PfRule::THEORY_PREPROCESS: return "THEORY_PREPROCESS";
    case PfRule::THEORY_PREPROCESS_LEMMA: return "THEORY_PREPROCESS_LEMMA";
    case PfRule::THEORY_EXPAND_DEF: return "THEORY_EXPAND_DEF";
    case PfRule::WITNESS_AXIOM: return "WITNESS_AXIOM";
    case PfRule::TRUST_REWRITE: return "TRUST_REWRITE";
    case PfRule::TRUST_FLATTENING_REWRITE: return "TRUST_FLATTENING_REWRITE";
    case PfRule::TRUST_SUBS: return "TRUST_SUBS";
    case PfRule::TRUST_SUBS_MAP: return "TRUST_SUBS_MAP";
    case PfRule::TRUST_SUBS_EQ: return "TRUST_SUBS_EQ";
    case PfRule::THEORY_INFERENCE: return "THEORY_INFERENCE";
    case PfRule::SAT_REFUTATION: return "SAT_REFUTATION";
    //================================================= Boolean rules
    case PfRule::RESOLUTION: return "RESOLUTION";
    case PfRule::CHAIN_RESOLUTION: return "CHAIN_RESOLUTION";
    case PfRule::FACTORING: return "FACTORING";
    case PfRule::REORDERING: return "REORDERING";
    case PfRule::MACRO_RESOLUTION: return "MACRO_RESOLUTION";
    case PfRule::MACRO_RESOLUTION_TRUST: return "MACRO_RESOLUTION_TRUST";
    case PfRule::SPLIT: return "SPLIT";
    case PfRule::EQ_RESOLVE: return "EQ_RESOLVE";
    case PfRule::MODUS_PONENS: return "MODUS_PONENS";
    case PfRule::NOT_NOT_ELIM: return "NOT_NOT_ELIM";
    case PfRule::CONTRA: return "CONTRA";
    case PfRule::AND_ELIM: return "AND_ELIM";
    case PfRule::AND_INTRO: return "AND_INTRO";
    case PfRule::NOT_OR_ELIM: return "NOT_OR_ELIM";
    case PfRule::IMPLIES_ELIM: return "IMPLIES_ELIM";
    case PfRule::NOT_IMPLIES_ELIM1: return "NOT_IMPLIES_ELIM1";
    case PfRule::NOT_IMPLIES_ELIM2: return "NOT_IMPLIES_ELIM2";
    case PfRule::EQUIV_ELIM1: return "EQUIV_ELIM1";
    case PfRule::EQUIV_ELIM2: return "EQUIV_ELIM2";
    case PfRule::NOT_EQUIV_ELIM1: return "NOT_EQUIV_ELIM1";
    case PfRule::NOT_EQUIV_ELIM2: return "NOT_EQUIV_ELIM2";
    case PfRule::XOR_ELIM1: return "XOR_ELIM1";
    case PfRule::XOR_ELIM2: return "XOR_ELIM2";
    case PfRule::NOT_XOR_ELIM1: return "NOT_XOR_ELIM1";
    case PfRule::NOT_XOR_ELIM2: return "NOT_XOR_ELIM2";
    case PfRule::ITE_ELIM1: return "ITE_ELIM1";
    case PfRule::ITE_ELIM2: return "ITE_ELIM2";
    case PfRule::NOT_ITE_ELIM1: return "NOT_ITE_ELIM1";
    case PfRule::NOT_ITE_ELIM2: return "NOT_ITE_ELIM2";
    case PfRule::NOT_AND: return "NOT_AND";
    //================================================= CNF rules
    case PfRule::CNF_AND_POS: return "CNF_AND_POS";
    case PfRule::CNF_AND_NEG: return "CNF_AND_NEG";
    case PfRule::CNF_OR_POS: return "CNF_OR_POS";
    case PfRule::CNF_OR_NEG: return "CNF_OR_NEG";
    case PfRule::CNF_IMPLIES_POS: return "CNF_IMPLIES_POS";
    case PfRule::CNF_IMPLIES_NEG1: return "CNF_IMPLIES_NEG1";
    case PfRule::CNF_IMPLIES_NEG2: return "CNF_IMPLIES_NEG2";
    case PfRule::CNF_EQUIV_POS1: return "CNF_EQUIV_POS1";
    case PfRule::CNF_EQUIV_POS2: return "CNF_EQUIV_POS2";
    case PfRule::CNF_EQUIV_NEG1: return "CNF_EQUIV_NEG1";
    case PfRule::CNF_EQUIV_NEG2: return "CNF_EQUIV_NEG2";
    case PfRule::CNF_XOR_POS1: return "CNF_XOR_POS1";
    case PfRule::CNF_XOR_POS2: return "CNF_XOR_POS2";
    case PfRule::CNF_XOR_NEG1: return "CNF_XOR_NEG1";
    case PfRule::CNF_XOR_NEG2: return "CNF_XOR_NEG2";
    case PfRule::CNF_ITE_POS1: return "CNF_ITE_POS1";
    case PfRule::CNF_ITE_POS2: return "CNF_ITE_POS2";
    case PfRule::CNF_ITE_POS3: return "CNF_ITE_POS3";
    case PfRule::CNF_ITE_NEG1: return "CNF_ITE_NEG1";
    case PfRule::CNF_ITE_NEG2: return "CNF_ITE_NEG2";
    case PfRule::CNF_ITE_NEG3: return "CNF_ITE_NEG3";
    //================================================= Equality rules
    case PfRule::REFL: return "REFL";
    case PfRule::SYMM: return "SYMM";
    case PfRule::TRANS: return "TRANS";
    case PfRule::CONG: return "CONG";
    case PfRule::TRUE_INTRO: return "TRUE_INTRO";
    case PfRule::TRUE_ELIM: return "TRUE_ELIM";
    case PfRule::FALSE_INTRO: return "FALSE_INTRO";
    case PfRule::FALSE_ELIM: return "FALSE_ELIM";
    case PfRule::HO_APP_ENCODE: return "HO_APP_ENCODE";
    case PfRule::HO_CONG: return "HO_CONG";
    case PfRule::BETA_REDUCE: return "BETA_REDUCE";
    //================================================= Array rules
    case PfRule::ARRAYS_READ_OVER_WRITE: return "ARRAYS_READ_OVER_WRITE";
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA:
      return "ARRAYS_READ_OVER_WRITE_CONTRA";
    case PfRule::ARRAYS_READ_OVER_WRITE_1: return "ARRAYS_READ_OVER_WRITE_1";
    case PfRule::ARRAYS_EXT: return "ARRAYS_EXT";
    case PfRule::ARRAYS_EQ_RANGE_EXPAND: return "ARRAYS_EQ_RANGE_EXPAND";
    //================================================= Bit-Vector rules
    case PfRule::BV_BITBLAST: return "BV_BITBLAST";
    case PfRule::BV_BITBLAST_STEP: return "BV_BITBLAST_STEP";
    case PfRule::BV_EAGER_ATOM: return "BV_EAGER_ATOM";
    //================================================= Datatype rules
    case PfRule::DT_UNIF: return "DT_UNIF";
    case PfRule::DT_INST: return "DT_INST";
    case PfRule::DT_COLLAPSE: return "DT_COLLAPSE";
    case PfRule::DT_SPLIT: return "DT_SPLIT";
    case PfRule::DT_CLASH: return "DT_CLASH";
    //================================================= Quantifiers rules
    case PfRule::SKOLEM_INTRO: return "SKOLEM_INTRO";
    case PfRule::SKOLEMIZE: return "SKOLEMIZE";
    case PfRule::INSTANTIATE: return "INSTANTIATE";
    case PfRule::ALPHA_EQUIV: return "ALPHA_EQUIV";
    case PfRule::QUANTIFIERS_PREPROCESS: return "QUANTIFIERS_PREPROCESS";
    //================================================= String rules
    case PfRule::CONCAT_EQ: return "CONCAT_EQ";
    case PfRule::CONCAT_UNIFY: return "CONCAT_UNIFY";
    case PfRule::CONCAT_CONFLICT: return "CONCAT_CONFLICT";
    case PfRule::CONCAT_SPLIT: return "CONCAT_SPLIT";
    case PfRule::CONCAT_CSPLIT: return "CONCAT_CSPLIT";
    case PfRule::CONCAT_LPROP: return "CONCAT_LPROP";
    case PfRule::CONCAT_CPROP: return "CONCAT_CPROP";
    case PfRule::STRING_DECOMPOSE: return "STRING_DECOMPOSE";
    case PfRule::STRING_LENGTH_POS: return "STRING_LENGTH_POS";
    case PfRule::STRING_LENGTH_NON_EMPTY: return "STRING_LENGTH_NON_EMPTY";
    case PfRule::STRING_REDUCTION: return "STRING_REDUCTION";
    case PfRule::STRING_EAGER_REDUCTION: return "STRING_EAGER_REDUCTION";
    case PfRule::RE_INTER: return "RE_INTER";
    case PfRule::RE_UNFOLD_POS: return "RE_UNFOLD_POS";
    case PfRule::RE_UNFOLD_NEG: return "RE_UNFOLD_NEG";
    case PfRule::RE_UNFOLD_NEG_CONCAT_FIXED:
      return "RE_UNFOLD_NEG_CONCAT_FIXED";
    case PfRule::RE_ELIM: return "RE_ELIM";
    case PfRule::STRING_CODE_INJ: return "STRING_CODE_INJ";
    case PfRule::STRING_SEQ_UNIT_INJ: return "STRING_SEQ_UNIT_INJ";
    case PfRule::STRING_INFERENCE: return "STRING_INFERENCE";
    //================================================= Arith rules
    case PfRule::MACRO_ARITH_SCALE_SUM_UB: return "MACRO_ARITH_SCALE_SUM_UB";
    case PfRule::ARITH_SUM_UB: return "ARITH_SUM_UB";
    case PfRule::ARITH_TRICHOTOMY: return "ARITH_TRICHOTOMY";
    case PfRule::INT_TIGHT_LB: return "INT_TIGHT_LB";
    case PfRule::INT_TIGHT_UB: return "INT_TIGHT_UB";
    case PfRule::ARITH_MULT_SIGN: return "ARITH_MULT_SIGN";
    case PfRule::ARITH_MULT_POS: return "ARITH_MULT_POS";
    case PfRule::ARITH_MULT_NEG: return "ARITH_MULT_NEG";
    case PfRule::ARITH_MULT_TANGENT: return "ARITH_MULT_TANGENT";
    case PfRule::ARITH_OP_ELIM_AXIOM: return "ARITH_OP_ELIM_AXIOM";
    case PfRule::ARITH_POLY_NORM: return "ARITH_POLY_NORM";
    case PfRule::ARITH_TRANS_PI: return "ARITH_TRANS_PI";
    case PfRule::ARITH_TRANS_EXP_NEG: return "ARITH_TRANS_EXP_NEG";
    case PfRule::ARITH_TRANS_EXP_POSITIVITY:
      return "ARITH_TRANS_EXP_POSITIVITY";
    case PfRule::ARITH_TRANS_EXP_SUPER_LIN: return "ARITH_TRANS_EXP_SUPER_LIN";
    case PfRule::ARITH_TRANS_EXP_ZERO: return "ARITH_TRANS_EXP_ZERO";
    case PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG:
      return "ARITH_TRANS_EXP_APPROX_ABOVE_NEG";
    case PfRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS:
      return "ARITH_TRANS_EXP_APPROX_ABOVE_POS";
    case PfRule::ARITH_TRANS_EXP_APPROX_BELOW:
      return "ARITH_TRANS_EXP_APPROX_BELOW";
    case PfRule::ARITH_TRANS_SINE_BOUNDS: return "ARITH_TRANS_SINE_BOUNDS";
    case PfRule::ARITH_TRANS_SINE_SHIFT: return "ARITH_TRANS_SINE_SHIFT";
    case PfRule::ARITH_TRANS_SINE_SYMMETRY: return "ARITH_TRANS_SINE_SYMMETRY";
    case PfRule::ARITH_TRANS_SINE_TANGENT_ZERO:
      return "ARITH_TRANS_SINE_TANGENT_ZERO";
    case PfRule::ARITH_TRANS_SINE_TANGENT_PI:
      return "ARITH_TRANS_SINE_TANGENT_PI";
    case PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG:
      return "ARITH_TRANS_SINE_APPROX_ABOVE_NEG";
    case PfRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS:
      return "ARITH_TRANS_SINE_APPROX_ABOVE_POS";
    case PfRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG:
      return "ARITH_TRANS_SINE_APPROX_BELOW_NEG";
    case PfRule::ARITH_TRANS_SINE_APPROX_BELOW_POS:
      return "ARITH_TRANS_SINE_APPROX_BELOW_POS";
    case PfRule::ARITH_NL_COVERING_DIRECT: return "ARITH_NL_COVERING_DIRECT";
    case PfRule::ARITH_NL_COVERING_RECURSIVE: return "ARITH_NL_COVERING_RECURSIVE";
    //================================================= External rules
    case PfRule::LFSC_RULE: return "LFSC_RULE";
    case PfRule::ALETHE_RULE: return "ALETHE_RULE";
    //================================================= Unknown rule
    case PfRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, PfRule id)
{
  out << toString(id);
  return out;
}

size_t PfRuleHashFunction::operator()(PfRule id) const
{
  return static_cast<size_t>(id);
}

}  // namespace cvc5::internal
