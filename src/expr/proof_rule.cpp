/*********************                                                        */
/*! \file proof_rule.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof rule
 **/

#include "expr/proof_rule.h"

#include <iostream>

namespace CVC4 {

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
    case PfRule::REMOVE_TERM_FORMULA_AXIOM: return "REMOVE_TERM_FORMULA_AXIOM";
    //================================================= Trusted rules
    case PfRule::THEORY_LEMMA: return "THEORY_LEMMA";
    case PfRule::THEORY_REWRITE: return "THEORY_REWRITE";
    case PfRule::PREPROCESS: return "PREPROCESS";
    case PfRule::PREPROCESS_LEMMA: return "PREPROCESS_LEMMA";
    case PfRule::THEORY_PREPROCESS: return "THEORY_PREPROCESS";
    case PfRule::THEORY_PREPROCESS_LEMMA: return "THEORY_PREPROCESS_LEMMA";
    case PfRule::WITNESS_AXIOM: return "WITNESS_AXIOM";
    //================================================= Boolean rules
    case PfRule::RESOLUTION: return "RESOLUTION";
    case PfRule::CHAIN_RESOLUTION: return "CHAIN_RESOLUTION";
    case PfRule::FACTORING: return "FACTORING";
    case PfRule::REORDERING: return "REORDERING";
    case PfRule::SPLIT: return "SPLIT";
    case PfRule::EQ_RESOLVE: return "EQ_RESOLVE";
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
    case PfRule::CONTRA: return "CONTRA";
    //================================================= De Morgan rules
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
    //================================================= Array rules
    case PfRule::ARRAYS_READ_OVER_WRITE: return "ARRAYS_READ_OVER_WRITE";
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA:
      return "ARRAYS_READ_OVER_WRITE_CONTRA";
    case PfRule::ARRAYS_READ_OVER_WRITE_1: return "ARRAYS_READ_OVER_WRITE_1";
    case PfRule::ARRAYS_EXT: return "ARRAYS_EXT";
    case PfRule::ARRAYS_TRUST: return "ARRAYS_TRUST";
    //================================================= Quantifiers rules
    case PfRule::WITNESS_INTRO: return "WITNESS_INTRO";
    case PfRule::EXISTS_INTRO: return "EXISTS_INTRO";
    case PfRule::SKOLEMIZE: return "SKOLEMIZE";
    case PfRule::INSTANTIATE: return "INSTANTIATE";
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
    case PfRule::STRING_TRUST: return "STRING_TRUST";
    //================================================= Arith rules
    case PfRule::ARITH_SCALE_SUM_UPPER_BOUNDS: return "ARITH_SCALE_SUM_UPPER_BOUNDS";
    case PfRule::ARITH_TRICHOTOMY: return "ARITH_TRICHOTOMY";
    case PfRule::INT_TIGHT_LB: return "INT_TIGHT_LB";
    case PfRule::INT_TIGHT_UB: return "INT_TIGHT_UB";
    case PfRule::INT_TRUST: return "INT_TRUST";
    case PfRule::ARITH_OP_ELIM_AXIOM: return "ARITH_OP_ELIM_AXIOM";
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

}  // namespace CVC4
