/*********************                                                        */
/*! \file proof_rule.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof rule
 **/

#include "expr/proof_rule.h"

#include <iostream>

namespace CVC4 {

const char* toString(ProofRule id)
{
  switch (id)
  {
    //================================================= Core rules
    case ProofRule::ASSUME: return "ASSUME";
    case ProofRule::SUBS: return "SUBS";
    case ProofRule::REWRITE: return "REWRITE";
    case ProofRule::SPLIT: return "SPLIT";
    //================================================= Equality rules
    case ProofRule::REFL: return "REFL";
    case ProofRule::SYMM: return "SYMM";
    case ProofRule::TRANS: return "TRANS";
    case ProofRule::CONG: return "CONG";
    //================================================= String rules
    case ProofRule::CONCAT_ENDP_UNIFY: return "CONCAT_ENDP_UNIFY";
    case ProofRule::CONCAT_UNIFY: return "CONCAT_UNIFY";
    case ProofRule::CONCAT_SPLIT: return "CONCAT_SPLIT";
    case ProofRule::CONCAT_LPROP: return "CONCAT_LPROP";
    case ProofRule::CONCAT_CPROP: return "CONCAT_CPROP";
    case ProofRule::CTN_NOT_EQUAL: return "CTN_NOT_EQUAL";
    case ProofRule::REDUCTION: return "REDUCTION";
    case ProofRule::RE_INTER: return "RE_INTER";
    case ProofRule::RE_UNFOLD: return "RE_UNFOLD";
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

}  // namespace CVC4
