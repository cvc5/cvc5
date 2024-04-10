/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof rule.
 */

#include <cvc5/cvc5_proof_rule.h>

#include <iostream>

namespace cvc5 {

const char* toString(ProofRule id)
{
  switch (id)
  {
    //================================================= Core rules
    case ProofRule::ASSUME: return "ASSUME";
    case ProofRule::SCOPE: return "SCOPE";
    case ProofRule::SUBS: return "SUBS";
    case ProofRule::MACRO_REWRITE: return "MACRO_REWRITE";
    case ProofRule::EVALUATE: return "EVALUATE";
    case ProofRule::ACI_NORM: return "ACI_NORM";
    case ProofRule::MACRO_SR_EQ_INTRO: return "MACRO_SR_EQ_INTRO";
    case ProofRule::MACRO_SR_PRED_INTRO: return "MACRO_SR_PRED_INTRO";
    case ProofRule::MACRO_SR_PRED_ELIM: return "MACRO_SR_PRED_ELIM";
    case ProofRule::MACRO_SR_PRED_TRANSFORM: return "MACRO_SR_PRED_TRANSFORM";
    case ProofRule::ENCODE_PRED_TRANSFORM: return "ENCODE_PRED_TRANSFORM";
    case ProofRule::ANNOTATION: return "ANNOTATION";
    case ProofRule::DSL_REWRITE: return "DSL_REWRITE";
    case ProofRule::REMOVE_TERM_FORMULA_AXIOM: return "REMOVE_TERM_FORMULA_AXIOM";
    //================================================= Trusted rules
    case ProofRule::TRUST: return "TRUST";
    case ProofRule::TRUST_THEORY_REWRITE: return "TRUST_THEORY_REWRITE";
    case ProofRule::SAT_REFUTATION: return "SAT_REFUTATION";
    case ProofRule::DRAT_REFUTATION: return "DRAT_REFUTATION";
    case ProofRule::SAT_EXTERNAL_PROVE: return "SAT_EXTERNAL_PROVE";
    //================================================= Boolean rules
    case ProofRule::RESOLUTION: return "RESOLUTION";
    case ProofRule::CHAIN_RESOLUTION: return "CHAIN_RESOLUTION";
    case ProofRule::FACTORING: return "FACTORING";
    case ProofRule::REORDERING: return "REORDERING";
    case ProofRule::MACRO_RESOLUTION: return "MACRO_RESOLUTION";
    case ProofRule::MACRO_RESOLUTION_TRUST: return "MACRO_RESOLUTION_TRUST";
    case ProofRule::SPLIT: return "SPLIT";
    case ProofRule::EQ_RESOLVE: return "EQ_RESOLVE";
    case ProofRule::MODUS_PONENS: return "MODUS_PONENS";
    case ProofRule::NOT_NOT_ELIM: return "NOT_NOT_ELIM";
    case ProofRule::CONTRA: return "CONTRA";
    case ProofRule::AND_ELIM: return "AND_ELIM";
    case ProofRule::AND_INTRO: return "AND_INTRO";
    case ProofRule::NOT_OR_ELIM: return "NOT_OR_ELIM";
    case ProofRule::IMPLIES_ELIM: return "IMPLIES_ELIM";
    case ProofRule::NOT_IMPLIES_ELIM1: return "NOT_IMPLIES_ELIM1";
    case ProofRule::NOT_IMPLIES_ELIM2: return "NOT_IMPLIES_ELIM2";
    case ProofRule::EQUIV_ELIM1: return "EQUIV_ELIM1";
    case ProofRule::EQUIV_ELIM2: return "EQUIV_ELIM2";
    case ProofRule::NOT_EQUIV_ELIM1: return "NOT_EQUIV_ELIM1";
    case ProofRule::NOT_EQUIV_ELIM2: return "NOT_EQUIV_ELIM2";
    case ProofRule::XOR_ELIM1: return "XOR_ELIM1";
    case ProofRule::XOR_ELIM2: return "XOR_ELIM2";
    case ProofRule::NOT_XOR_ELIM1: return "NOT_XOR_ELIM1";
    case ProofRule::NOT_XOR_ELIM2: return "NOT_XOR_ELIM2";
    case ProofRule::ITE_ELIM1: return "ITE_ELIM1";
    case ProofRule::ITE_ELIM2: return "ITE_ELIM2";
    case ProofRule::NOT_ITE_ELIM1: return "NOT_ITE_ELIM1";
    case ProofRule::NOT_ITE_ELIM2: return "NOT_ITE_ELIM2";
    case ProofRule::NOT_AND: return "NOT_AND";
    //================================================= CNF rules
    case ProofRule::CNF_AND_POS: return "CNF_AND_POS";
    case ProofRule::CNF_AND_NEG: return "CNF_AND_NEG";
    case ProofRule::CNF_OR_POS: return "CNF_OR_POS";
    case ProofRule::CNF_OR_NEG: return "CNF_OR_NEG";
    case ProofRule::CNF_IMPLIES_POS: return "CNF_IMPLIES_POS";
    case ProofRule::CNF_IMPLIES_NEG1: return "CNF_IMPLIES_NEG1";
    case ProofRule::CNF_IMPLIES_NEG2: return "CNF_IMPLIES_NEG2";
    case ProofRule::CNF_EQUIV_POS1: return "CNF_EQUIV_POS1";
    case ProofRule::CNF_EQUIV_POS2: return "CNF_EQUIV_POS2";
    case ProofRule::CNF_EQUIV_NEG1: return "CNF_EQUIV_NEG1";
    case ProofRule::CNF_EQUIV_NEG2: return "CNF_EQUIV_NEG2";
    case ProofRule::CNF_XOR_POS1: return "CNF_XOR_POS1";
    case ProofRule::CNF_XOR_POS2: return "CNF_XOR_POS2";
    case ProofRule::CNF_XOR_NEG1: return "CNF_XOR_NEG1";
    case ProofRule::CNF_XOR_NEG2: return "CNF_XOR_NEG2";
    case ProofRule::CNF_ITE_POS1: return "CNF_ITE_POS1";
    case ProofRule::CNF_ITE_POS2: return "CNF_ITE_POS2";
    case ProofRule::CNF_ITE_POS3: return "CNF_ITE_POS3";
    case ProofRule::CNF_ITE_NEG1: return "CNF_ITE_NEG1";
    case ProofRule::CNF_ITE_NEG2: return "CNF_ITE_NEG2";
    case ProofRule::CNF_ITE_NEG3: return "CNF_ITE_NEG3";
    //================================================= Equality rules
    case ProofRule::REFL: return "REFL";
    case ProofRule::SYMM: return "SYMM";
    case ProofRule::TRANS: return "TRANS";
    case ProofRule::CONG: return "CONG";
    case ProofRule::NARY_CONG: return "NARY_CONG";
    case ProofRule::TRUE_INTRO: return "TRUE_INTRO";
    case ProofRule::TRUE_ELIM: return "TRUE_ELIM";
    case ProofRule::FALSE_INTRO: return "FALSE_INTRO";
    case ProofRule::FALSE_ELIM: return "FALSE_ELIM";
    case ProofRule::HO_APP_ENCODE: return "HO_APP_ENCODE";
    case ProofRule::HO_CONG: return "HO_CONG";
    case ProofRule::BETA_REDUCE: return "BETA_REDUCE";
    //================================================= Array rules
    case ProofRule::ARRAYS_READ_OVER_WRITE: return "ARRAYS_READ_OVER_WRITE";
    case ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA:
      return "ARRAYS_READ_OVER_WRITE_CONTRA";
    case ProofRule::ARRAYS_READ_OVER_WRITE_1: return "ARRAYS_READ_OVER_WRITE_1";
    case ProofRule::ARRAYS_EXT: return "ARRAYS_EXT";
    case ProofRule::ARRAYS_EQ_RANGE_EXPAND: return "ARRAYS_EQ_RANGE_EXPAND";
    //================================================= Bit-Vector rules
    case ProofRule::MACRO_BV_BITBLAST: return "MACRO_BV_BITBLAST";
    case ProofRule::BV_BITBLAST_STEP: return "BV_BITBLAST_STEP";
    case ProofRule::BV_EAGER_ATOM: return "BV_EAGER_ATOM";
    //================================================= Datatype rules
    case ProofRule::DT_UNIF: return "DT_UNIF";
    case ProofRule::DT_INST: return "DT_INST";
    case ProofRule::DT_COLLAPSE: return "DT_COLLAPSE";
    case ProofRule::DT_SPLIT: return "DT_SPLIT";
    case ProofRule::DT_CLASH: return "DT_CLASH";
    //================================================= Quantifiers rules
    case ProofRule::SKOLEM_INTRO: return "SKOLEM_INTRO";
    case ProofRule::SKOLEMIZE: return "SKOLEMIZE";
    case ProofRule::INSTANTIATE: return "INSTANTIATE";
    case ProofRule::ALPHA_EQUIV: return "ALPHA_EQUIV";
    //================================================= String rules
    case ProofRule::CONCAT_EQ: return "CONCAT_EQ";
    case ProofRule::CONCAT_UNIFY: return "CONCAT_UNIFY";
    case ProofRule::CONCAT_CONFLICT: return "CONCAT_CONFLICT";
    case ProofRule::CONCAT_CONFLICT_DEQ: return "CONCAT_CONFLICT_DEQ";
    case ProofRule::CONCAT_SPLIT: return "CONCAT_SPLIT";
    case ProofRule::CONCAT_CSPLIT: return "CONCAT_CSPLIT";
    case ProofRule::CONCAT_LPROP: return "CONCAT_LPROP";
    case ProofRule::CONCAT_CPROP: return "CONCAT_CPROP";
    case ProofRule::STRING_DECOMPOSE: return "STRING_DECOMPOSE";
    case ProofRule::STRING_LENGTH_POS: return "STRING_LENGTH_POS";
    case ProofRule::STRING_LENGTH_NON_EMPTY: return "STRING_LENGTH_NON_EMPTY";
    case ProofRule::STRING_REDUCTION: return "STRING_REDUCTION";
    case ProofRule::STRING_EAGER_REDUCTION: return "STRING_EAGER_REDUCTION";
    case ProofRule::RE_INTER: return "RE_INTER";
    case ProofRule::RE_UNFOLD_POS: return "RE_UNFOLD_POS";
    case ProofRule::RE_UNFOLD_NEG: return "RE_UNFOLD_NEG";
    case ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED:
      return "RE_UNFOLD_NEG_CONCAT_FIXED";
    case ProofRule::RE_ELIM: return "RE_ELIM";
    case ProofRule::STRING_CODE_INJ: return "STRING_CODE_INJ";
    case ProofRule::STRING_SEQ_UNIT_INJ: return "STRING_SEQ_UNIT_INJ";
    case ProofRule::MACRO_STRING_INFERENCE: return "MACRO_STRING_INFERENCE";
    //================================================= Arith rules
    case ProofRule::MACRO_ARITH_SCALE_SUM_UB: return "MACRO_ARITH_SCALE_SUM_UB";
    case ProofRule::ARITH_SUM_UB: return "ARITH_SUM_UB";
    case ProofRule::ARITH_TRICHOTOMY: return "ARITH_TRICHOTOMY";
    case ProofRule::INT_TIGHT_LB: return "INT_TIGHT_LB";
    case ProofRule::INT_TIGHT_UB: return "INT_TIGHT_UB";
    case ProofRule::ARITH_MULT_SIGN: return "ARITH_MULT_SIGN";
    case ProofRule::ARITH_MULT_POS: return "ARITH_MULT_POS";
    case ProofRule::ARITH_MULT_NEG: return "ARITH_MULT_NEG";
    case ProofRule::ARITH_MULT_TANGENT: return "ARITH_MULT_TANGENT";
    case ProofRule::ARITH_OP_ELIM_AXIOM: return "ARITH_OP_ELIM_AXIOM";
    case ProofRule::ARITH_POLY_NORM: return "ARITH_POLY_NORM";
    case ProofRule::ARITH_TRANS_PI: return "ARITH_TRANS_PI";
    case ProofRule::ARITH_TRANS_EXP_NEG: return "ARITH_TRANS_EXP_NEG";
    case ProofRule::ARITH_TRANS_EXP_POSITIVITY:
      return "ARITH_TRANS_EXP_POSITIVITY";
    case ProofRule::ARITH_TRANS_EXP_SUPER_LIN: return "ARITH_TRANS_EXP_SUPER_LIN";
    case ProofRule::ARITH_TRANS_EXP_ZERO: return "ARITH_TRANS_EXP_ZERO";
    case ProofRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG:
      return "ARITH_TRANS_EXP_APPROX_ABOVE_NEG";
    case ProofRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS:
      return "ARITH_TRANS_EXP_APPROX_ABOVE_POS";
    case ProofRule::ARITH_TRANS_EXP_APPROX_BELOW:
      return "ARITH_TRANS_EXP_APPROX_BELOW";
    case ProofRule::ARITH_TRANS_SINE_BOUNDS: return "ARITH_TRANS_SINE_BOUNDS";
    case ProofRule::ARITH_TRANS_SINE_SHIFT: return "ARITH_TRANS_SINE_SHIFT";
    case ProofRule::ARITH_TRANS_SINE_SYMMETRY: return "ARITH_TRANS_SINE_SYMMETRY";
    case ProofRule::ARITH_TRANS_SINE_TANGENT_ZERO:
      return "ARITH_TRANS_SINE_TANGENT_ZERO";
    case ProofRule::ARITH_TRANS_SINE_TANGENT_PI:
      return "ARITH_TRANS_SINE_TANGENT_PI";
    case ProofRule::ARITH_TRANS_SINE_APPROX_ABOVE_NEG:
      return "ARITH_TRANS_SINE_APPROX_ABOVE_NEG";
    case ProofRule::ARITH_TRANS_SINE_APPROX_ABOVE_POS:
      return "ARITH_TRANS_SINE_APPROX_ABOVE_POS";
    case ProofRule::ARITH_TRANS_SINE_APPROX_BELOW_NEG:
      return "ARITH_TRANS_SINE_APPROX_BELOW_NEG";
    case ProofRule::ARITH_TRANS_SINE_APPROX_BELOW_POS:
      return "ARITH_TRANS_SINE_APPROX_BELOW_POS";
    case ProofRule::ARITH_NL_COVERING_DIRECT: return "ARITH_NL_COVERING_DIRECT";
    case ProofRule::ARITH_NL_COVERING_RECURSIVE: return "ARITH_NL_COVERING_RECURSIVE";
    //================================================= External rules
    case ProofRule::LFSC_RULE: return "LFSC_RULE";
    case ProofRule::ALETHE_RULE: return "ALETHE_RULE";
    //================================================= Unknown rule
    case ProofRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofRule id)
{
  out << toString(id);
  return out;
}
}  // namespace cvc5

namespace std {

size_t hash<cvc5::ProofRule>::operator()(cvc5::ProofRule rule) const
{
  return static_cast<size_t>(rule);
}

}  // namespace std
