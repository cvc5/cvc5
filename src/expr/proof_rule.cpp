/*********************                                                        */
/*! \file proof_step.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof step
 **/

#include "expr/proof_step.h"

namespace CVC4 {

const char* toString(ProofStep id)
{
  switch (id)
  {
    //================================================= Core rules
    case ProofStep::ASSUME: return "ASSUME";
    case ProofStep::SUBS: return "SUBS";
    case ProofStep::REWRITE: return "REWRITE";
    case ProofStep::SPLIT: return "SPLIT";
    //================================================= Equality rules
    case ProofStep::REFL: return "REFL";
    case ProofStep::SYMM: return "SYMM";
    case ProofStep::TRANS: return "TRANS";
    case ProofStep::CONG: return "CONG";
    //================================================= String rules
    case ProofStep::CONCAT_ENDP_UNIFY: return "CONCAT_ENDP_UNIFY";
    case ProofStep::CONCAT_UNIFY: return "CONCAT_UNIFY";
    case ProofStep::CONCAT_SPLIT: return "CONCAT_SPLIT";
    case ProofStep::CONCAT_LPROP: return "CONCAT_LPROP";
    case ProofStep::CONCAT_CPROP: return "CONCAT_CPROP";
    case ProofStep::CTN_NOT_EQUAL: return "CTN_NOT_EQUAL";
    case ProofStep::REDUCTION: return "REDUCTION";
    case ProofStep::RE_INTER: return "RE_INTER";
    case ProofStep::RE_UNFOLD: return "RE_UNFOLD";
    //================================================= Unknown rule
    case ProofStep::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofStep id)
{
  out << toString(id);
  return out;
}

}  // namespace CVC4
