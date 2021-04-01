/*********************                                                        */
/*! \file verit_proof_rule.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of veriT proof rules
 **/

#include "proof/verit/verit_proof_rule.h"

#include <iostream>

namespace cvc5 {

namespace proof {

const char* veritRuletoString(VeritRule id)
{
  switch (id)
  {
    case VeritRule::UNDEFINED: return "undefined";
    case VeritRule::ASSUME: return "assume";
    case VeritRule::ANCHOR: return "anchor";
    case VeritRule::INPUT: return "input";
    case VeritRule::TRUE: return "true";
    case VeritRule::FALSE: return "false";
    case VeritRule::NOT_NOT: return "not_not";
    case VeritRule::AND_POS: return "and_pos";
    case VeritRule::AND_NEG: return "and_neg";
    case VeritRule::OR_POS: return "or_pos";
    case VeritRule::OR_NEG: return "or_neg";
    case VeritRule::XOR_POS1: return "xor_pos1";
    case VeritRule::XOR_POS2: return "xor_pos2";
    case VeritRule::XOR_NEG1: return "xor_neg1";
    case VeritRule::XOR_NEG2: return "xor_neg2";
    case VeritRule::IMPLIES_POS: return "implies_pos";
    case VeritRule::IMPLIES_NEG1: return "implies_neg1";
    case VeritRule::IMPLIES_NEG2: return "implies_neg2";
    case VeritRule::EQUIV_POS1: return "equiv_pos1";
    case VeritRule::EQUIV_POS2: return "equiv_pos2";
    case VeritRule::EQUIV_NEG1: return "equiv_neg1";
    case VeritRule::EQUIV_NEG2: return "equiv_neg2";
    case VeritRule::ITE_POS1: return "ite_pos1";
    case VeritRule::ITE_POS2: return "ite_pos2";
    case VeritRule::ITE_NEG1: return "ite_neg1";
    case VeritRule::ITE_NEG2: return "ite_neg2";
    case VeritRule::EQ_REFLEXIVE: return "eq_reflexive";
    case VeritRule::EQ_TRANSITIVE: return "eq_transitive";
    case VeritRule::EQ_CONGRUENT: return "eq_congruent";
    case VeritRule::EQ_CONGRUENT_PRED: return "eq_congruent_pred";
    case VeritRule::DISTINCT_ELIM: return "distinct_elim";
    case VeritRule::LA_RW_EQ: return "la_rw_eq";
    case VeritRule::LA_GENERIC: return "la_generic";
    case VeritRule::LIA_GENERIC: return "lia_generic";
    case VeritRule::LA_DISEQUALITY: return "la_disequality";
    case VeritRule::LA_TOTALITY: return "la_totality";
    case VeritRule::LA_TAUTOLOGY: return "la_tautology";
    case VeritRule::FORALL_INST: return "forall_inst";
    case VeritRule::QNT_JOIN: return "qnt_join";
    case VeritRule::QNT_RM_UNUSED: return "qnt_rm_unused";
    case VeritRule::TH_RESOLUTION: return "th_resolution";
    case VeritRule::RESOLUTION: return "resolution";
    case VeritRule::REFL: return "refl";
    case VeritRule::TRANS: return "trans";
    case VeritRule::CONG: return "cong";
    case VeritRule::AND: return "and";
    case VeritRule::TAUTOLOGIC_CLAUSE: return "tautologic_clause";
    case VeritRule::NOT_OR: return "not_or";
    case VeritRule::OR: return "or";
    case VeritRule::NOT_AND: return "not_and";
    case VeritRule::XOR1: return "xor1";
    case VeritRule::XOR2: return "xor2";
    case VeritRule::NOT_XOR1: return "not_xor1";
    case VeritRule::NOT_XOR2: return "not_xor2";
    case VeritRule::IMPLIES: return "implies";
    case VeritRule::NOT_IMPLIES1: return "not_implies1";
    case VeritRule::NOT_IMPLIES2: return "not_implies2";
    case VeritRule::EQUIV1: return "equiv1";
    case VeritRule::EQUIV2: return "equiv2";
    case VeritRule::NOT_EQUIV1: return "not_equiv1";
    case VeritRule::NOT_EQUIV2: return "not_equiv2";
    case VeritRule::ITE1: return "ite1";
    case VeritRule::ITE2: return "ite2";
    case VeritRule::NOT_ITE1: return "not_ite1";
    case VeritRule::NOT_ITE2: return "not_ite2";
    case VeritRule::ITE_INTRO: return "ite_intro";
    case VeritRule::DUPLICATE_LITERALS: return "duplicate_literals";
    case VeritRule::CONNECTIVE_DEF: return "connective_def";
    case VeritRule::ITE_SIMPLIFY: return "ite_simplify";
    case VeritRule::EQ_SIMPLIFY: return "eq_simplify";
    case VeritRule::AND_SIMPLIFY: return "and_simplify";
    case VeritRule::OR_SIMPLIFY: return "or_simplify";
    case VeritRule::NOT_SIMPLIFY: return "not_simplify";
    case VeritRule::IMPLIES_SIMPLIFY: return "implies_simplify";
    case VeritRule::EQUIV_SIMPLIFY: return "equiv_simplify";
    case VeritRule::BOOL_SIMPLIFY: return "bool_simplify";
    case VeritRule::QUANTIFIER_SIMPLIFY: return "quantifier_simplify";
    case VeritRule::DIV_SIMPLIFY: return "div_simplify";
    case VeritRule::PROD_SIMPLIFY: return "prod_simplify";
    case VeritRule::UNARY_MINUS_SIMPLIFY: return "unary_minus_simplify";
    case VeritRule::MINUS_SIMPLIFY: return "minus_simplify";
    case VeritRule::SUM_SIMPLIFY: return "sum_simplify";
    case VeritRule::COMP_SIMPLIFY: return "comp_simplify";
    case VeritRule::NARY_ELIM: return "nary_elim";
    case VeritRule::TMP_AC_SIMP: return "tmp_ac_simp";
    case VeritRule::TMP_BFUN_ELIM: return "tmp_bfun-elim";
    case VeritRule::TEMP_QUANTIFIER_CNF: return "tmp_quantifier_cnf";
    case VeritRule::SUBPROOF: return "subproof";
    case VeritRule::BIND: return "bind";
    case VeritRule::LET: return "let";
    case VeritRule::QNT_SIMPLIFY: return "qnt_simplify";
    case VeritRule::SKO_EX: return "sko_ex";
    case VeritRule::SKO_FORALL: return "sko_forall";
    default: return "?";
  }
}

}  // namespace proof

}  // namespace cvc5
