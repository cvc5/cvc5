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

const char* toString(ProofRule rule)
{
  switch (rule)
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
    case ProofRule::REMOVE_TERM_FORMULA_AXIOM:
      return "REMOVE_TERM_FORMULA_AXIOM";
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
    case ProofRule::ARITH_TRANS_EXP_SUPER_LIN:
      return "ARITH_TRANS_EXP_SUPER_LIN";
    case ProofRule::ARITH_TRANS_EXP_ZERO: return "ARITH_TRANS_EXP_ZERO";
    case ProofRule::ARITH_TRANS_EXP_APPROX_ABOVE_NEG:
      return "ARITH_TRANS_EXP_APPROX_ABOVE_NEG";
    case ProofRule::ARITH_TRANS_EXP_APPROX_ABOVE_POS:
      return "ARITH_TRANS_EXP_APPROX_ABOVE_POS";
    case ProofRule::ARITH_TRANS_EXP_APPROX_BELOW:
      return "ARITH_TRANS_EXP_APPROX_BELOW";
    case ProofRule::ARITH_TRANS_SINE_BOUNDS: return "ARITH_TRANS_SINE_BOUNDS";
    case ProofRule::ARITH_TRANS_SINE_SHIFT: return "ARITH_TRANS_SINE_SHIFT";
    case ProofRule::ARITH_TRANS_SINE_SYMMETRY:
      return "ARITH_TRANS_SINE_SYMMETRY";
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
    case ProofRule::ARITH_NL_COVERING_RECURSIVE:
      return "ARITH_NL_COVERING_RECURSIVE";
    //================================================= External rules
    case ProofRule::LFSC_RULE: return "LFSC_RULE";
    case ProofRule::ALETHE_RULE: return "ALETHE_RULE";
    //================================================= Unknown rule
    case ProofRule::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofRule rule)
{
  out << toString(rule);
  return out;
}

const char* toString(cvc5::ProofRewriteRule rule)
{
  switch (rule)
  {
    case ProofRewriteRule::NONE:
      return "NONE";
      //================================================= RARE rule
      // ${printer}$
    case ProofRewriteRule::ARITH_PLUS_ZERO: return "arith-plus-zero";
    case ProofRewriteRule::ARITH_MUL_ONE: return "arith-mul-one";
    case ProofRewriteRule::ARITH_MUL_ZERO: return "arith-mul-zero";
    case ProofRewriteRule::ARITH_INT_DIV_ONE: return "arith-int-div-one";
    case ProofRewriteRule::ARITH_NEG_NEG_ONE: return "arith-neg-neg-one";
    case ProofRewriteRule::ARITH_ELIM_UMINUS: return "arith-elim-uminus";
    case ProofRewriteRule::ARITH_ELIM_MINUS: return "arith-elim-minus";
    case ProofRewriteRule::ARITH_ELIM_GT: return "arith-elim-gt";
    case ProofRewriteRule::ARITH_ELIM_LT: return "arith-elim-lt";
    case ProofRewriteRule::ARITH_ELIM_LEQ: return "arith-elim-leq";
    case ProofRewriteRule::ARITH_LEQ_NORM: return "arith-leq-norm";
    case ProofRewriteRule::ARITH_GEQ_TIGHTEN: return "arith-geq-tighten";
    case ProofRewriteRule::ARITH_GEQ_NORM: return "arith-geq-norm";
    case ProofRewriteRule::ARITH_REFL_LEQ: return "arith-refl-leq";
    case ProofRewriteRule::ARITH_REFL_LT: return "arith-refl-lt";
    case ProofRewriteRule::ARITH_REFL_GEQ: return "arith-refl-geq";
    case ProofRewriteRule::ARITH_REFL_GT: return "arith-refl-gt";
    case ProofRewriteRule::ARITH_PLUS_FLATTEN: return "arith-plus-flatten";
    case ProofRewriteRule::ARITH_MULT_FLATTEN: return "arith-mult-flatten";
    case ProofRewriteRule::ARITH_MULT_DIST: return "arith-mult-dist";
    case ProofRewriteRule::ARITH_PLUS_CANCEL1: return "arith-plus-cancel1";
    case ProofRewriteRule::ARITH_PLUS_CANCEL2: return "arith-plus-cancel2";
    case ProofRewriteRule::ARRAY_READ_OVER_WRITE:
      return "array-read-over-write";
    case ProofRewriteRule::ARRAY_READ_OVER_WRITE2:
      return "array-read-over-write2";
    case ProofRewriteRule::ARRAY_STORE_OVERWRITE:
      return "array-store-overwrite";
    case ProofRewriteRule::ARRAY_STORE_SELF: return "array-store-self";
    case ProofRewriteRule::BOOL_DOUBLE_NOT_ELIM: return "bool-double-not-elim";
    case ProofRewriteRule::BOOL_EQ_TRUE: return "bool-eq-true";
    case ProofRewriteRule::BOOL_EQ_FALSE: return "bool-eq-false";
    case ProofRewriteRule::BOOL_EQ_NREFL: return "bool-eq-nrefl";
    case ProofRewriteRule::BOOL_IMPL_FALSE1: return "bool-impl-false1";
    case ProofRewriteRule::BOOL_IMPL_FALSE2: return "bool-impl-false2";
    case ProofRewriteRule::BOOL_IMPL_TRUE1: return "bool-impl-true1";
    case ProofRewriteRule::BOOL_IMPL_TRUE2: return "bool-impl-true2";
    case ProofRewriteRule::BOOL_IMPL_ELIM: return "bool-impl-elim";
    case ProofRewriteRule::BOOL_OR_TRUE: return "bool-or-true";
    case ProofRewriteRule::BOOL_OR_FALSE: return "bool-or-false";
    case ProofRewriteRule::BOOL_OR_FLATTEN: return "bool-or-flatten";
    case ProofRewriteRule::BOOL_OR_DUP: return "bool-or-dup";
    case ProofRewriteRule::BOOL_AND_TRUE: return "bool-and-true";
    case ProofRewriteRule::BOOL_AND_FALSE: return "bool-and-false";
    case ProofRewriteRule::BOOL_AND_FLATTEN: return "bool-and-flatten";
    case ProofRewriteRule::BOOL_AND_DUP: return "bool-and-dup";
    case ProofRewriteRule::BOOL_AND_CONF: return "bool-and-conf";
    case ProofRewriteRule::BOOL_OR_TAUT: return "bool-or-taut";
    case ProofRewriteRule::BOOL_XOR_REFL: return "bool-xor-refl";
    case ProofRewriteRule::BOOL_XOR_NREFL: return "bool-xor-nrefl";
    case ProofRewriteRule::BOOL_XOR_FALSE: return "bool-xor-false";
    case ProofRewriteRule::BOOL_XOR_TRUE: return "bool-xor-true";
    case ProofRewriteRule::BOOL_XOR_COMM: return "bool-xor-comm";
    case ProofRewriteRule::BOOL_XOR_ELIM: return "bool-xor-elim";
    case ProofRewriteRule::ITE_NEG_BRANCH: return "ite-neg-branch";
    case ProofRewriteRule::ITE_THEN_TRUE: return "ite-then-true";
    case ProofRewriteRule::ITE_ELSE_FALSE: return "ite-else-false";
    case ProofRewriteRule::ITE_THEN_FALSE: return "ite-then-false";
    case ProofRewriteRule::ITE_ELSE_TRUE: return "ite-else-true";
    case ProofRewriteRule::ITE_THEN_LOOKAHEAD_SELF:
      return "ite-then-lookahead-self";
    case ProofRewriteRule::ITE_ELSE_LOOKAHEAD_SELF:
      return "ite-else-lookahead-self";
    case ProofRewriteRule::ITE_TRUE_COND: return "ite-true-cond";
    case ProofRewriteRule::ITE_FALSE_COND: return "ite-false-cond";
    case ProofRewriteRule::ITE_NOT_COND: return "ite-not-cond";
    case ProofRewriteRule::ITE_EQ_BRANCH: return "ite-eq-branch";
    case ProofRewriteRule::ITE_THEN_LOOKAHEAD: return "ite-then-lookahead";
    case ProofRewriteRule::ITE_ELSE_LOOKAHEAD: return "ite-else-lookahead";
    case ProofRewriteRule::ITE_THEN_NEG_LOOKAHEAD:
      return "ite-then-neg-lookahead";
    case ProofRewriteRule::ITE_ELSE_NEG_LOOKAHEAD:
      return "ite-else-neg-lookahead";
    case ProofRewriteRule::BV_CONCAT_FLATTEN: return "bv-concat-flatten";
    case ProofRewriteRule::BV_CONCAT_EXTRACT_MERGE:
      return "bv-concat-extract-merge";
    case ProofRewriteRule::BV_EXTRACT_EXTRACT: return "bv-extract-extract";
    case ProofRewriteRule::BV_EXTRACT_WHOLE: return "bv-extract-whole";
    case ProofRewriteRule::BV_EXTRACT_CONCAT_1: return "bv-extract-concat-1";
    case ProofRewriteRule::BV_EXTRACT_CONCAT_2: return "bv-extract-concat-2";
    case ProofRewriteRule::BV_EXTRACT_CONCAT_3: return "bv-extract-concat-3";
    case ProofRewriteRule::BV_EXTRACT_CONCAT_4: return "bv-extract-concat-4";
    case ProofRewriteRule::BV_EXTRACT_BITWISE_AND:
      return "bv-extract-bitwise-and";
    case ProofRewriteRule::BV_EXTRACT_BITWISE_OR:
      return "bv-extract-bitwise-or";
    case ProofRewriteRule::BV_EXTRACT_BITWISE_XOR:
      return "bv-extract-bitwise-xor";
    case ProofRewriteRule::BV_EXTRACT_NOT: return "bv-extract-not";
    case ProofRewriteRule::BV_EXTRACT_SIGN_EXTEND_1:
      return "bv-extract-sign-extend-1";
    case ProofRewriteRule::BV_EXTRACT_SIGN_EXTEND_2:
      return "bv-extract-sign-extend-2";
    case ProofRewriteRule::BV_EXTRACT_SIGN_EXTEND_3:
      return "bv-extract-sign-extend-3";
    case ProofRewriteRule::BV_NEG_MULT: return "bv-neg-mult";
    case ProofRewriteRule::BV_NEG_ADD: return "bv-neg-add";
    case ProofRewriteRule::BV_MULT_DISTRIB_CONST_NEG:
      return "bv-mult-distrib-const-neg";
    case ProofRewriteRule::BV_MULT_DISTRIB_CONST_ADD:
      return "bv-mult-distrib-const-add";
    case ProofRewriteRule::BV_MULT_DISTRIB_CONST_SUB:
      return "bv-mult-distrib-const-sub";
    case ProofRewriteRule::BV_MULT_DISTRIB_1: return "bv-mult-distrib-1";
    case ProofRewriteRule::BV_MULT_DISTRIB_2: return "bv-mult-distrib-2";
    case ProofRewriteRule::BV_NOT_XOR: return "bv-not-xor";
    case ProofRewriteRule::BV_AND_SIMPLIFY_1: return "bv-and-simplify-1";
    case ProofRewriteRule::BV_AND_SIMPLIFY_2: return "bv-and-simplify-2";
    case ProofRewriteRule::BV_OR_SIMPLIFY_1: return "bv-or-simplify-1";
    case ProofRewriteRule::BV_OR_SIMPLIFY_2: return "bv-or-simplify-2";
    case ProofRewriteRule::BV_XOR_SIMPLIFY_1: return "bv-xor-simplify-1";
    case ProofRewriteRule::BV_XOR_SIMPLIFY_2: return "bv-xor-simplify-2";
    case ProofRewriteRule::BV_XOR_SIMPLIFY_3: return "bv-xor-simplify-3";
    case ProofRewriteRule::BV_ULT_ADD_ONE: return "bv-ult-add-one";
    case ProofRewriteRule::BV_CONCAT_TO_MULT: return "bv-concat-to-mult";
    case ProofRewriteRule::BV_MULT_SLT_MULT_1: return "bv-mult-slt-mult-1";
    case ProofRewriteRule::BV_MULT_SLT_MULT_2: return "bv-mult-slt-mult-2";
    case ProofRewriteRule::BV_COMMUTATIVE_AND: return "bv-commutative-and";
    case ProofRewriteRule::BV_COMMUTATIVE_OR: return "bv-commutative-or";
    case ProofRewriteRule::BV_COMMUTATIVE_XOR: return "bv-commutative-xor";
    case ProofRewriteRule::BV_COMMUTATIVE_MUL: return "bv-commutative-mul";
    case ProofRewriteRule::BV_OR_ZERO: return "bv-or-zero";
    case ProofRewriteRule::BV_MUL_ONE: return "bv-mul-one";
    case ProofRewriteRule::BV_MUL_ZERO: return "bv-mul-zero";
    case ProofRewriteRule::BV_ADD_ZERO: return "bv-add-zero";
    case ProofRewriteRule::BV_ADD_TWO: return "bv-add-two";
    case ProofRewriteRule::BV_ZERO_EXTEND_ELIMINATE_0:
      return "bv-zero-extend-eliminate-0";
    case ProofRewriteRule::BV_SIGN_EXTEND_ELIMINATE_0:
      return "bv-sign-extend-eliminate-0";
    case ProofRewriteRule::BV_NOT_NEQ: return "bv-not-neq";
    case ProofRewriteRule::BV_ULT_ONES: return "bv-ult-ones";
    case ProofRewriteRule::BV_OR_FLATTEN: return "bv-or-flatten";
    case ProofRewriteRule::BV_XOR_FLATTEN: return "bv-xor-flatten";
    case ProofRewriteRule::BV_AND_FLATTEN: return "bv-and-flatten";
    case ProofRewriteRule::BV_MUL_FLATTEN: return "bv-mul-flatten";
    case ProofRewriteRule::BV_CONCAT_MERGE_CONST:
      return "bv-concat-merge-const";
    case ProofRewriteRule::BV_COMMUTATIVE_ADD: return "bv-commutative-add";
    case ProofRewriteRule::BV_NEG_SUB: return "bv-neg-sub";
    case ProofRewriteRule::BV_NEG_IDEMP: return "bv-neg-idemp";
    case ProofRewriteRule::BV_SUB_ELIMINATE: return "bv-sub-eliminate";
    case ProofRewriteRule::BV_UGT_ELIMINATE: return "bv-ugt-eliminate";
    case ProofRewriteRule::BV_UGE_ELIMINATE: return "bv-uge-eliminate";
    case ProofRewriteRule::BV_SGT_ELIMINATE: return "bv-sgt-eliminate";
    case ProofRewriteRule::BV_SGE_ELIMINATE: return "bv-sge-eliminate";
    case ProofRewriteRule::BV_SLT_ELIMINATE: return "bv-slt-eliminate";
    case ProofRewriteRule::BV_SLE_ELIMINATE: return "bv-sle-eliminate";
    case ProofRewriteRule::BV_REDOR_ELIMINATE: return "bv-redor-eliminate";
    case ProofRewriteRule::BV_REDAND_ELIMINATE: return "bv-redand-eliminate";
    case ProofRewriteRule::BV_ULE_ELIMINATE: return "bv-ule-eliminate";
    case ProofRewriteRule::BV_COMP_ELIMINATE: return "bv-comp-eliminate";
    case ProofRewriteRule::BV_REPEAT_ELIMINATE_1:
      return "bv-repeat-eliminate-1";
    case ProofRewriteRule::BV_REPEAT_ELIMINATE_2:
      return "bv-repeat-eliminate-2";
    case ProofRewriteRule::BV_ROTATE_LEFT_ELIMINATE_1:
      return "bv-rotate-left-eliminate-1";
    case ProofRewriteRule::BV_ROTATE_LEFT_ELIMINATE_2:
      return "bv-rotate-left-eliminate-2";
    case ProofRewriteRule::BV_ROTATE_RIGHT_ELIMINATE_1:
      return "bv-rotate-right-eliminate-1";
    case ProofRewriteRule::BV_ROTATE_RIGHT_ELIMINATE_2:
      return "bv-rotate-right-eliminate-2";
    case ProofRewriteRule::BV_NAND_ELIMINATE: return "bv-nand-eliminate";
    case ProofRewriteRule::BV_NOR_ELIMINATE: return "bv-nor-eliminate";
    case ProofRewriteRule::BV_XNOR_ELIMINATE: return "bv-xnor-eliminate";
    case ProofRewriteRule::BV_SDIV_ELIMINATE: return "bv-sdiv-eliminate";
    case ProofRewriteRule::BV_SDIV_ELIMINATE_FEWER_BITWISE_OPS:
      return "bv-sdiv-eliminate-fewer-bitwise-ops";
    case ProofRewriteRule::BV_ZERO_EXTEND_ELIMINATE:
      return "bv-zero-extend-eliminate";
    case ProofRewriteRule::BV_SIGN_EXTEND_ELIMINATE:
      return "bv-sign-extend-eliminate";
    case ProofRewriteRule::BV_UADDO_ELIMINATE: return "bv-uaddo-eliminate";
    case ProofRewriteRule::BV_SADDO_ELIMINATE: return "bv-saddo-eliminate";
    case ProofRewriteRule::BV_SDIVO_ELIMINATE: return "bv-sdivo-eliminate";
    case ProofRewriteRule::BV_SMOD_ELIMINATE: return "bv-smod-eliminate";
    case ProofRewriteRule::BV_SMOD_ELIMINATE_FEWER_BITWISE_OPS:
      return "bv-smod-eliminate-fewer-bitwise-ops";
    case ProofRewriteRule::BV_SREM_ELIMINATE: return "bv-srem-eliminate";
    case ProofRewriteRule::BV_SREM_ELIMINATE_FEWER_BITWISE_OPS:
      return "bv-srem-eliminate-fewer-bitwise-ops";
    case ProofRewriteRule::BV_USUBO_ELIMINATE: return "bv-usubo-eliminate";
    case ProofRewriteRule::BV_SSUBO_ELIMINATE: return "bv-ssubo-eliminate";
    case ProofRewriteRule::BV_ITE_EQUAL_CHILDREN:
      return "bv-ite-equal-children";
    case ProofRewriteRule::BV_ITE_CONST_CHILDREN_1:
      return "bv-ite-const-children-1";
    case ProofRewriteRule::BV_ITE_CONST_CHILDREN_2:
      return "bv-ite-const-children-2";
    case ProofRewriteRule::BV_ITE_EQUAL_COND_1: return "bv-ite-equal-cond-1";
    case ProofRewriteRule::BV_ITE_EQUAL_COND_2: return "bv-ite-equal-cond-2";
    case ProofRewriteRule::BV_ITE_EQUAL_COND_3: return "bv-ite-equal-cond-3";
    case ProofRewriteRule::BV_ITE_MERGE_THEN_IF: return "bv-ite-merge-then-if";
    case ProofRewriteRule::BV_ITE_MERGE_ELSE_IF: return "bv-ite-merge-else-if";
    case ProofRewriteRule::BV_ITE_MERGE_THEN_ELSE:
      return "bv-ite-merge-then-else";
    case ProofRewriteRule::BV_ITE_MERGE_ELSE_ELSE:
      return "bv-ite-merge-else-else";
    case ProofRewriteRule::BV_SHL_BY_CONST_0: return "bv-shl-by-const-0";
    case ProofRewriteRule::BV_SHL_BY_CONST_1: return "bv-shl-by-const-1";
    case ProofRewriteRule::BV_SHL_BY_CONST_2: return "bv-shl-by-const-2";
    case ProofRewriteRule::BV_LSHR_BY_CONST_0: return "bv-lshr-by-const-0";
    case ProofRewriteRule::BV_LSHR_BY_CONST_1: return "bv-lshr-by-const-1";
    case ProofRewriteRule::BV_LSHR_BY_CONST_2: return "bv-lshr-by-const-2";
    case ProofRewriteRule::BV_ASHR_BY_CONST_0: return "bv-ashr-by-const-0";
    case ProofRewriteRule::BV_ASHR_BY_CONST_1: return "bv-ashr-by-const-1";
    case ProofRewriteRule::BV_ASHR_BY_CONST_2: return "bv-ashr-by-const-2";
    case ProofRewriteRule::BV_AND_CONCAT_PULLUP: return "bv-and-concat-pullup";
    case ProofRewriteRule::BV_OR_CONCAT_PULLUP: return "bv-or-concat-pullup";
    case ProofRewriteRule::BV_XOR_CONCAT_PULLUP: return "bv-xor-concat-pullup";
    case ProofRewriteRule::BV_BITWISE_IDEMP_1: return "bv-bitwise-idemp-1";
    case ProofRewriteRule::BV_BITWISE_IDEMP_2: return "bv-bitwise-idemp-2";
    case ProofRewriteRule::BV_AND_ZERO: return "bv-and-zero";
    case ProofRewriteRule::BV_AND_ONE: return "bv-and-one";
    case ProofRewriteRule::BV_OR_ONE: return "bv-or-one";
    case ProofRewriteRule::BV_XOR_DUPLICATE: return "bv-xor-duplicate";
    case ProofRewriteRule::BV_XOR_ONES: return "bv-xor-ones";
    case ProofRewriteRule::BV_XOR_ZERO: return "bv-xor-zero";
    case ProofRewriteRule::BV_BITWISE_NOT_AND: return "bv-bitwise-not-and";
    case ProofRewriteRule::BV_BITWISE_NOT_OR: return "bv-bitwise-not-or";
    case ProofRewriteRule::BV_XOR_NOT: return "bv-xor-not";
    case ProofRewriteRule::BV_NOT_IDEMP: return "bv-not-idemp";
    case ProofRewriteRule::BV_ULT_ZERO_1: return "bv-ult-zero-1";
    case ProofRewriteRule::BV_ULT_ZERO_2: return "bv-ult-zero-2";
    case ProofRewriteRule::BV_ULT_SELF: return "bv-ult-self";
    case ProofRewriteRule::BV_LT_SELF: return "bv-lt-self";
    case ProofRewriteRule::BV_ULE_SELF: return "bv-ule-self";
    case ProofRewriteRule::BV_ULE_ZERO: return "bv-ule-zero";
    case ProofRewriteRule::BV_ZERO_ULE: return "bv-zero-ule";
    case ProofRewriteRule::BV_SLE_SELF: return "bv-sle-self";
    case ProofRewriteRule::BV_ULE_MAX: return "bv-ule-max";
    case ProofRewriteRule::BV_NOT_ULT: return "bv-not-ult";
    case ProofRewriteRule::BV_NOT_ULE: return "bv-not-ule";
    case ProofRewriteRule::BV_NOT_SLE: return "bv-not-sle";
    case ProofRewriteRule::BV_MULT_POW2_1: return "bv-mult-pow2-1";
    case ProofRewriteRule::BV_MULT_POW2_2: return "bv-mult-pow2-2";
    case ProofRewriteRule::BV_MULT_POW2_2B: return "bv-mult-pow2-2b";
    case ProofRewriteRule::BV_EXTRACT_MULT_LEADING_BIT:
      return "bv-extract-mult-leading-bit";
    case ProofRewriteRule::BV_UDIV_POW2_NOT_ONE: return "bv-udiv-pow2-not-one";
    case ProofRewriteRule::BV_UDIV_ZERO: return "bv-udiv-zero";
    case ProofRewriteRule::BV_UDIV_ONE: return "bv-udiv-one";
    case ProofRewriteRule::BV_UREM_POW2_NOT_ONE: return "bv-urem-pow2-not-one";
    case ProofRewriteRule::BV_UREM_ONE: return "bv-urem-one";
    case ProofRewriteRule::BV_UREM_SELF: return "bv-urem-self";
    case ProofRewriteRule::BV_SHL_ZERO: return "bv-shl-zero";
    case ProofRewriteRule::BV_LSHR_ZERO: return "bv-lshr-zero";
    case ProofRewriteRule::BV_ASHR_ZERO: return "bv-ashr-zero";
    case ProofRewriteRule::BV_UGT_UREM: return "bv-ugt-urem";
    case ProofRewriteRule::BV_ULT_ONE: return "bv-ult-one";
    case ProofRewriteRule::BV_SLT_ZERO: return "bv-slt-zero";
    case ProofRewriteRule::BV_MERGE_SIGN_EXTEND_1:
      return "bv-merge-sign-extend-1";
    case ProofRewriteRule::BV_MERGE_SIGN_EXTEND_2:
      return "bv-merge-sign-extend-2";
    case ProofRewriteRule::BV_MERGE_SIGN_EXTEND_3:
      return "bv-merge-sign-extend-3";
    case ProofRewriteRule::BV_SIGN_EXTEND_EQ_CONST_1:
      return "bv-sign-extend-eq-const-1";
    case ProofRewriteRule::BV_SIGN_EXTEND_EQ_CONST_2:
      return "bv-sign-extend-eq-const-2";
    case ProofRewriteRule::BV_ZERO_EXTEND_EQ_CONST_1:
      return "bv-zero-extend-eq-const-1";
    case ProofRewriteRule::BV_ZERO_EXTEND_EQ_CONST_2:
      return "bv-zero-extend-eq-const-2";
    case ProofRewriteRule::BV_ZERO_EXTEND_ULT_CONST_1:
      return "bv-zero-extend-ult-const-1";
    case ProofRewriteRule::BV_ZERO_EXTEND_ULT_CONST_2:
      return "bv-zero-extend-ult-const-2";
    case ProofRewriteRule::BV_SIGN_EXTEND_ULT_CONST_1:
      return "bv-sign-extend-ult-const-1";
    case ProofRewriteRule::BV_SIGN_EXTEND_ULT_CONST_2:
      return "bv-sign-extend-ult-const-2";
    case ProofRewriteRule::BV_SIGN_EXTEND_ULT_CONST_3:
      return "bv-sign-extend-ult-const-3";
    case ProofRewriteRule::BV_SIGN_EXTEND_ULT_CONST_4:
      return "bv-sign-extend-ult-const-4";
    case ProofRewriteRule::SETS_MEMBER_SINGLETON:
      return "sets-member-singleton";
    case ProofRewriteRule::SETS_SUBSET_ELIM: return "sets-subset-elim";
    case ProofRewriteRule::SETS_UNION_COMM: return "sets-union-comm";
    case ProofRewriteRule::SETS_INTER_COMM: return "sets-inter-comm";
    case ProofRewriteRule::SETS_INTER_MEMBER: return "sets-inter-member";
    case ProofRewriteRule::SETS_MINUS_MEMBER: return "sets-minus-member";
    case ProofRewriteRule::SETS_UNION_MEMBER: return "sets-union-member";
    case ProofRewriteRule::STR_EQ_CTN_FALSE: return "str-eq-ctn-false";
    case ProofRewriteRule::STR_CONCAT_FLATTEN: return "str-concat-flatten";
    case ProofRewriteRule::STR_CONCAT_FLATTEN_EQ:
      return "str-concat-flatten-eq";
    case ProofRewriteRule::STR_CONCAT_FLATTEN_EQ_REV:
      return "str-concat-flatten-eq-rev";
    case ProofRewriteRule::STR_SUBSTR_EMPTY_STR: return "str-substr-empty-str";
    case ProofRewriteRule::STR_SUBSTR_EMPTY_RANGE:
      return "str-substr-empty-range";
    case ProofRewriteRule::STR_SUBSTR_EMPTY_START:
      return "str-substr-empty-start";
    case ProofRewriteRule::STR_SUBSTR_EMPTY_START_NEG:
      return "str-substr-empty-start-neg";
    case ProofRewriteRule::STR_SUBSTR_EQ_EMPTY: return "str-substr-eq-empty";
    case ProofRewriteRule::STR_LEN_REPLACE_INV: return "str-len-replace-inv";
    case ProofRewriteRule::STR_LEN_UPDATE_INV: return "str-len-update-inv";
    case ProofRewriteRule::STR_LEN_SUBSTR_IN_RANGE:
      return "str-len-substr-in-range";
    case ProofRewriteRule::STR_LEN_SUBSTR_UB1: return "str-len-substr-ub1";
    case ProofRewriteRule::STR_LEN_SUBSTR_UB2: return "str-len-substr-ub2";
    case ProofRewriteRule::RE_IN_EMPTY: return "re-in-empty";
    case ProofRewriteRule::RE_IN_SIGMA: return "re-in-sigma";
    case ProofRewriteRule::RE_IN_SIGMA_STAR: return "re-in-sigma-star";
    case ProofRewriteRule::RE_IN_CSTRING: return "re-in-cstring";
    case ProofRewriteRule::RE_IN_COMP: return "re-in-comp";
    case ProofRewriteRule::STR_CONCAT_CLASH: return "str-concat-clash";
    case ProofRewriteRule::STR_CONCAT_CLASH_REV: return "str-concat-clash-rev";
    case ProofRewriteRule::STR_CONCAT_CLASH2: return "str-concat-clash2";
    case ProofRewriteRule::STR_CONCAT_CLASH2_REV:
      return "str-concat-clash2-rev";
    case ProofRewriteRule::STR_CONCAT_UNIFY: return "str-concat-unify";
    case ProofRewriteRule::STR_CONCAT_UNIFY_REV: return "str-concat-unify-rev";
    case ProofRewriteRule::STR_CONCAT_CLASH_CHAR:
      return "str-concat-clash-char";
    case ProofRewriteRule::STR_CONCAT_CLASH_CHAR_REV:
      return "str-concat-clash-char-rev";
    case ProofRewriteRule::STR_PREFIXOF_ELIM: return "str-prefixof-elim";
    case ProofRewriteRule::STR_SUFFIXOF_ELIM: return "str-suffixof-elim";
    case ProofRewriteRule::STR_PREFIXOF_ONE: return "str-prefixof-one";
    case ProofRewriteRule::STR_SUFFIXOF_ONE: return "str-suffixof-one";
    case ProofRewriteRule::STR_SUBSTR_COMBINE1: return "str-substr-combine1";
    case ProofRewriteRule::STR_SUBSTR_COMBINE2: return "str-substr-combine2";
    case ProofRewriteRule::STR_SUBSTR_CONCAT1: return "str-substr-concat1";
    case ProofRewriteRule::STR_SUBSTR_FULL: return "str-substr-full";
    case ProofRewriteRule::STR_CONTAINS_REFL: return "str-contains-refl";
    case ProofRewriteRule::STR_CONTAINS_CONCAT_FIND:
      return "str-contains-concat-find";
    case ProofRewriteRule::STR_CONTAINS_SPLIT_CHAR:
      return "str-contains-split-char";
    case ProofRewriteRule::STR_CONTAINS_LEQ_LEN_EQ:
      return "str-contains-leq-len-eq";
    case ProofRewriteRule::STR_CONCAT_EMP: return "str-concat-emp";
    case ProofRewriteRule::STR_AT_ELIM: return "str-at-elim";
    case ProofRewriteRule::RE_ALL_ELIM: return "re-all-elim";
    case ProofRewriteRule::RE_OPT_ELIM: return "re-opt-elim";
    case ProofRewriteRule::RE_CONCAT_EMP: return "re-concat-emp";
    case ProofRewriteRule::RE_CONCAT_NONE: return "re-concat-none";
    case ProofRewriteRule::RE_CONCAT_FLATTEN: return "re-concat-flatten";
    case ProofRewriteRule::RE_CONCAT_STAR_SWAP: return "re-concat-star-swap";
    case ProofRewriteRule::RE_UNION_ALL: return "re-union-all";
    case ProofRewriteRule::RE_UNION_NONE: return "re-union-none";
    case ProofRewriteRule::RE_UNION_FLATTEN: return "re-union-flatten";
    case ProofRewriteRule::RE_UNION_DUP: return "re-union-dup";
    case ProofRewriteRule::RE_INTER_ALL: return "re-inter-all";
    case ProofRewriteRule::RE_INTER_NONE: return "re-inter-none";
    case ProofRewriteRule::RE_INTER_FLATTEN: return "re-inter-flatten";
    case ProofRewriteRule::RE_INTER_DUP: return "re-inter-dup";
    case ProofRewriteRule::STR_LEN_CONCAT_REC: return "str-len-concat-rec";
    case ProofRewriteRule::STR_IN_RE_RANGE_ELIM: return "str-in-re-range-elim";
    case ProofRewriteRule::SEQ_LEN_UNIT: return "seq-len-unit";
    case ProofRewriteRule::SEQ_NTH_UNIT: return "seq-nth-unit";
    case ProofRewriteRule::SEQ_REV_UNIT: return "seq-rev-unit";
    case ProofRewriteRule::EQ_REFL: return "eq-refl";
    case ProofRewriteRule::EQ_SYMM: return "eq-symm";
    case ProofRewriteRule::DISTINCT_BINARY_ELIM:
      return "distinct-binary-elim";
      // ${printer}$
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofRewriteRule rule)
{
  out << toString(rule);
  return out;
}

}  // namespace cvc5

namespace std {

size_t hash<cvc5::ProofRule>::operator()(cvc5::ProofRule rule) const
{
  return static_cast<size_t>(rule);
}

std::string to_string(cvc5::ProofRule rule) { return cvc5::toString(rule); }

size_t hash<cvc5::ProofRewriteRule>::operator()(
    cvc5::ProofRewriteRule rule) const
{
  return static_cast<size_t>(rule);
}

std::string to_string(cvc5::ProofRewriteRule rule)
{
  return cvc5::toString(rule);
}

}  // namespace std
