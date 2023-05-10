/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe proof rules
 */

#include "proof/alethe/alethe_proof_rule.h"

#include <iostream>

#include "proof/proof_checker.h"

namespace cvc5::internal {

namespace proof {

const char* aletheRuleToString(AletheRule id)
{
  switch (id)
  {
    case AletheRule::ASSUME: return "assume";
    case AletheRule::ANCHOR_SUBPROOF: return "subproof";
    case AletheRule::ANCHOR_BIND: return "bind";
    case AletheRule::ANCHOR_SKO_FORALL: return "sko_forall";
    case AletheRule::ANCHOR_SKO_EX: return "sko_ex";
    case AletheRule::TRUE: return "true";
    case AletheRule::FALSE: return "false";
    case AletheRule::NOT_NOT: return "not_not";
    case AletheRule::AND_POS: return "and_pos";
    case AletheRule::AND_NEG: return "and_neg";
    case AletheRule::OR_POS: return "or_pos";
    case AletheRule::OR_NEG: return "or_neg";
    case AletheRule::XOR_POS1: return "xor_pos1";
    case AletheRule::XOR_POS2: return "xor_pos2";
    case AletheRule::XOR_NEG1: return "xor_neg1";
    case AletheRule::XOR_NEG2: return "xor_neg2";
    case AletheRule::IMPLIES_POS: return "implies_pos";
    case AletheRule::IMPLIES_NEG1: return "implies_neg1";
    case AletheRule::IMPLIES_NEG2: return "implies_neg2";
    case AletheRule::EQUIV_POS1: return "equiv_pos1";
    case AletheRule::EQUIV_POS2: return "equiv_pos2";
    case AletheRule::EQUIV_NEG1: return "equiv_neg1";
    case AletheRule::EQUIV_NEG2: return "equiv_neg2";
    case AletheRule::ITE_POS1: return "ite_pos1";
    case AletheRule::ITE_POS2: return "ite_pos2";
    case AletheRule::ITE_NEG1: return "ite_neg1";
    case AletheRule::ITE_NEG2: return "ite_neg2";
    case AletheRule::EQ_REFLEXIVE: return "eq_reflexive";
    case AletheRule::EQ_TRANSITIVE: return "eq_transitive";
    case AletheRule::EQ_CONGRUENT: return "eq_congruent";
    case AletheRule::EQ_CONGRUENT_PRED: return "eq_congruent_pred";
    case AletheRule::DISTINCT_ELIM: return "distinct_elim";
    case AletheRule::LA_RW_EQ: return "la_rw_eq";
    case AletheRule::LA_GENERIC: return "la_generic";
    case AletheRule::LA_MULT_POS: return "la_mult_pos";
    case AletheRule::LA_MULT_NEG: return "la_mult_neg";
    case AletheRule::LIA_GENERIC: return "lia_generic";
    case AletheRule::LA_DISEQUALITY: return "la_disequality";
    case AletheRule::LA_TOTALITY: return "la_totality";
    case AletheRule::LA_TAUTOLOGY: return "la_tautology";
    case AletheRule::FORALL_INST: return "forall_inst";
    case AletheRule::QNT_JOIN: return "qnt_join";
    case AletheRule::QNT_RM_UNUSED: return "qnt_rm_unused";
    case AletheRule::TH_RESOLUTION: return "th_resolution";
    case AletheRule::RESOLUTION: return "resolution";
    case AletheRule::RESOLUTION_OR: return "resolution";
    case AletheRule::REFL: return "refl";
    case AletheRule::TRANS: return "trans";
    case AletheRule::CONG: return "cong";
    case AletheRule::AND: return "and";
    case AletheRule::TAUTOLOGIC_CLAUSE: return "tautologic_clause";
    case AletheRule::NOT_OR: return "not_or";
    case AletheRule::OR: return "or";
    case AletheRule::NOT_AND: return "not_and";
    case AletheRule::XOR1: return "xor1";
    case AletheRule::XOR2: return "xor2";
    case AletheRule::NOT_XOR1: return "not_xor1";
    case AletheRule::NOT_XOR2: return "not_xor2";
    case AletheRule::IMPLIES: return "implies";
    case AletheRule::NOT_IMPLIES1: return "not_implies1";
    case AletheRule::NOT_IMPLIES2: return "not_implies2";
    case AletheRule::EQUIV1: return "equiv1";
    case AletheRule::EQUIV2: return "equiv2";
    case AletheRule::NOT_EQUIV1: return "not_equiv1";
    case AletheRule::NOT_EQUIV2: return "not_equiv2";
    case AletheRule::ITE1: return "ite1";
    case AletheRule::ITE2: return "ite2";
    case AletheRule::NOT_ITE1: return "not_ite1";
    case AletheRule::NOT_ITE2: return "not_ite2";
    case AletheRule::ITE_INTRO: return "ite_intro";
    case AletheRule::CONTRACTION: return "contraction";
    case AletheRule::CONNECTIVE_DEF: return "connective_def";
    case AletheRule::ITE_SIMPLIFY: return "ite_simplify";
    case AletheRule::EQ_SIMPLIFY: return "eq_simplify";
    case AletheRule::AND_SIMPLIFY: return "and_simplify";
    case AletheRule::OR_SIMPLIFY: return "or_simplify";
    case AletheRule::NOT_SIMPLIFY: return "not_simplify";
    case AletheRule::IMPLIES_SIMPLIFY: return "implies_simplify";
    case AletheRule::EQUIV_SIMPLIFY: return "equiv_simplify";
    case AletheRule::BOOL_SIMPLIFY: return "bool_simplify";
    case AletheRule::QUANTIFIER_SIMPLIFY: return "qnt_simplify";
    case AletheRule::DIV_SIMPLIFY: return "div_simplify";
    case AletheRule::PROD_SIMPLIFY: return "prod_simplify";
    case AletheRule::UNARY_MINUS_SIMPLIFY: return "unary_minus_simplify";
    case AletheRule::MINUS_SIMPLIFY: return "minus_simplify";
    case AletheRule::SUM_SIMPLIFY: return "sum_simplify";
    case AletheRule::COMP_SIMPLIFY: return "comp_simplify";
    case AletheRule::NARY_ELIM: return "nary_elim";
    case AletheRule::LET: return "let";
    case AletheRule::QNT_SIMPLIFY: return "qnt_simplify";
    case AletheRule::SKO_EX: return "sko_ex";
    case AletheRule::SKO_FORALL: return "sko_forall";
    case AletheRule::ALL_SIMPLIFY: return "all_simplify";
    case AletheRule::SYMM: return "symm";
    case AletheRule::NOT_SYMM: return "not_symm";
    case AletheRule::REORDERING: return "reordering";
    case AletheRule::BV_BITBLAST_STEP_VAR: return "bv_bitblast_step_var";
    case AletheRule::BV_BITBLAST_STEP_BVAND: return "bv_bitblast_step_bvand";
    case AletheRule::BV_BITBLAST_STEP_BVOR: return "bv_bitblast_step_bvor";
    case AletheRule::BV_BITBLAST_STEP_BVXOR: return "bv_bitblast_step_bvxor";
    case AletheRule::BV_BITBLAST_STEP_BVXNOR: return "bv_bitblast_step_bvxnor";
    case AletheRule::BV_BITBLAST_STEP_BVNOT: return "bv_bitblast_step_bvnot";
    case AletheRule::BV_BITBLAST_STEP_BVADD: return "bv_bitblast_step_bvadd";
    case AletheRule::BV_BITBLAST_STEP_BVNEG: return "bv_bitblast_step_bvneg";
    case AletheRule::BV_BITBLAST_STEP_BVMULT: return "bv_bitblast_step_bvmult";
    case AletheRule::BV_BITBLAST_STEP_BVULE: return "bv_bitblast_step_bvule";
    case AletheRule::BV_BITBLAST_STEP_BVULT: return "bv_bitblast_step_bvult";
    case AletheRule::BV_BITBLAST_STEP_EXTRACT:
      return "bv_bitblast_step_extract";
    case AletheRule::BV_BITBLAST_STEP_BVEQUAL:
      return "bv_bitblast_step_bvequal";
    case AletheRule::BV_BITBLAST_STEP_CONCAT: return "bv_bitblast_step_concat";
    case AletheRule::BV_BITBLAST_STEP_CONST: return "bv_bitblast_step_const";
    //================================================= Hole
    case AletheRule::HOLE: return "hole";
    //================================================= Undefined rule
    case AletheRule::UNDEFINED: return "undefined";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, AletheRule id)
{
  out << aletheRuleToString(id);
  return out;
}

AletheRule getAletheRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<AletheRule>(id);
  }
  return AletheRule::UNDEFINED;
}

}  // namespace proof

}  // namespace cvc5::internal
