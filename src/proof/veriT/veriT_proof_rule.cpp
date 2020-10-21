/*********************                                                        */
/*! \file veriT_proof_rule.cpp
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

#include "proof/veriT/veriT_proof_rule.h"
#include<iostream>

namespace CVC4 {

namespace proof {

//TODO: Put in cpp, rename, change static
const char* veriTRuletoString(VeriTRule id)
{
  switch (id)
  {
  case VeriTRule::UNDEFINED: return "undefined";
	case VeriTRule::ASSUME: return "assume";
	case VeriTRule::ANCHOR: return "anchor";	
  case VeriTRule::INPUT: return "input";
  case VeriTRule::TRUE: return "true";
  case VeriTRule::FALSE: return "false";
  case VeriTRule::NOT_NOT: return "not_not";
  case VeriTRule::AND_POS: return "and_pos";
  case VeriTRule::AND_NEG: return "and_neg";    
  case VeriTRule::OR_POS: return "or_pos";  
  case VeriTRule::OR_NEG: return "or_neg";
  case VeriTRule::XOR_POS1: return "xor_pos1";    
  case VeriTRule::XOR_POS2: return "xor_pos2";    
  case VeriTRule::XOR_NEG1: return "xor_neg1";      
  case VeriTRule::XOR_NEG2: return "xor_neg2";
  case VeriTRule::IMPLIES_POS: return "implies_pos";
  case VeriTRule::IMPLIES_NEG1: return "implies_neg1";
  case VeriTRule::IMPLIES_NEG2: return "implies_neg2";
  case VeriTRule::EQUIV_POS1: return "equiv_pos1";
  case VeriTRule::EQUIV_POS2: return "equiv_pos2";
  case VeriTRule::EQUIV_NEG1: return "equiv_neg1";
  case VeriTRule::EQUIV_NEG2: return "equiv_neg2";
  case VeriTRule::ITE_POS1: return "ite_pos1";
  case VeriTRule::ITE_POS2: return "ite_pos2";
  case VeriTRule::ITE_NEG1: return "ite_neg1";
  case VeriTRule::ITE_NEG2: return "ite_neg2";
  case VeriTRule::EQ_REFLEXIVE: return "eq_reflexive";
  case VeriTRule::EQ_TRANSITIVE: return "eq_transitive";
  case VeriTRule::EQ_CONGRUENT: return "eq_congruent";
  case VeriTRule::EQ_CONGRUENT_PRED: return "eq_congruent_pred";
  case VeriTRule::DISTINCT_ELIM: return "distinct_elim";
  case VeriTRule::LA_RW_EQ: return "la_rw_eq";
  case VeriTRule::LA_GENERIC: return "la_generic";
  case VeriTRule::LIA_GENERIC: return "lia_generic";
  case VeriTRule::LA_DISEQUALITY: return "la_disequality";
  case VeriTRule::LA_TOTALITY: return "la_totality";
  case VeriTRule::LA_TAUTOLOGY: return "la_tautology";
  case VeriTRule::FORALL_INST: return "forall_inst";
  case VeriTRule::QNT_JOIN: return "qnt_join";
  case VeriTRule::QNT_RM_UNUSED: return "qnt_rm_unused";
  case VeriTRule::TH_RESOLUTION: return "th_resolution";
  case VeriTRule::RESOLUTION: return "resolution";
  case VeriTRule::REFL: return "refl";
  case VeriTRule::TRANS: return "trans";
  case VeriTRule::CONG: return "cong";
  case VeriTRule::AND: return "and";
  case VeriTRule::TAUTOLOGIC_CLAUSE: return "tautologic_clause";
  case VeriTRule::NOT_OR: return "not_or";
  case VeriTRule::OR: return "or";
  case VeriTRule::NOT_AND: return "not_and";
  case VeriTRule::XOR1: return "xor1";
  case VeriTRule::XOR2: return "xor2";
  case VeriTRule::NOT_XOR1: return "not_xor1";
  case VeriTRule::NOT_XOR2: return "not_xor2";
  case VeriTRule::IMPLIES: return "implies";
  case VeriTRule::NOT_IMPLIES1: return "not_implies1";
  case VeriTRule::NOT_IMPLIES2: return "not_implies2";
  case VeriTRule::EQUIV1: return "equiv1";
  case VeriTRule::EQUIV2: return "equiv2";
  case VeriTRule::NOT_EQUIV1: return "not_equiv1";
  case VeriTRule::NOT_EQUIV2: return "not_equiv2";
  case VeriTRule::ITE1: return "ite1";
  case VeriTRule::ITE2: return "ite2";
  case VeriTRule::NOT_ITE1: return "not_ite1";
  case VeriTRule::NOT_ITE2: return "not_ite2";
  case VeriTRule::ITE_INTRO: return "ite_intro";
  case VeriTRule::DUPLICATE_LITERALS: return "duplicate_literals";
  case VeriTRule::CONNECTIVE_DEF: return "connective_def";
  case VeriTRule::ITE_SIMPLIFY: return "ite_simplify";
  case VeriTRule::EQ_SIMPLIFY: return "eq_simplify";
  case VeriTRule::AND_SIMPLIFY: return "and_simplify";
  case VeriTRule::OR_SIMPLIFY: return "or_simplify";
  case VeriTRule::NOT_SIMPLIFY: return "not_simplify";
  case VeriTRule::IMPLIES_SIMPLIFY: return "implies_simplify";
  case VeriTRule::EQUIV_SIMPLIFY: return "equiv_simplify";
  case VeriTRule::BOOL_SIMPLIFY: return "bool_simplify";
  case VeriTRule::QUANTIFIER_SIMPLIFY: return "quantifier_simplify";
  case VeriTRule::DIV_SIMPLIFY: return "div_simplify";
  case VeriTRule::PROD_SIMPLIFY: return "prod_simplify";
  case VeriTRule::UNARY_MINUS_SIMPLIFY: return "unary_minus_simplify";
  case VeriTRule::MINUS_SIMPLIFY: return "minus_simplify";
  case VeriTRule::SUM_SIMPLIFY: return "sum_simplify";
  case VeriTRule::COMP_SIMPLIFY: return "comp_simplify";
  case VeriTRule::NARY_ELIM: return "nary_elim";
  case VeriTRule::TMP_AC_SIMP: return "tmp_ac_simp";
  case VeriTRule::TMP_BFUN_ELIM: return "tmp_bfun-elim";
  case VeriTRule::TMP_SKOLEMIZE: return "tmp_skolemize";
  case VeriTRule::TEMP_QUANTIFIER_CNF: return "tmp_quantifier_cnf";
  case VeriTRule::SUBPROOF: return "subproof";
  case VeriTRule::BIND: return "bind";
  case VeriTRule::LET: return "let";
  case VeriTRule::QNT_SIMPLIFY: return "qnt_simplify";
  case VeriTRule::SKO_EX: return "sko_ex";
  case VeriTRule::SKO_FORALL: return "sko_forall";
  default: return "?";
  }
}

} // namespace proof

} // namespace CVC4
