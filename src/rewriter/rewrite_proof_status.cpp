/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The status of a rewrite rule proof reconstruction attempt
 */

#include "rewriter/rewrite_proof_status.h"

namespace cvc5::internal {
namespace rewriter {

const char* toString(RewriteProofStatus s)
{
  switch (s)
  {
    case RewriteProofStatus::FAIL: return "FAIL";
    case RewriteProofStatus::REFL: return "REFL";
    case RewriteProofStatus::EVAL: return "EVAL";
    case RewriteProofStatus::TRANS: return "TRANS";
    case RewriteProofStatus::CONG: return "CONG";
    case RewriteProofStatus::CONG_EVAL: return "CONG_EVAL";
    case RewriteProofStatus::TRUE_ELIM: return "TRUE_ELIM";
    case RewriteProofStatus::TRUE_INTRO: return "TRUE_INTRO";
    case RewriteProofStatus::ARITH_POLY_NORM: return "ARITH_POLY_NORM";
    case RewriteProofStatus::ACI_NORM: return "ACI_NORM";
    case RewriteProofStatus::ABSORB: return "ABSORB";
    case RewriteProofStatus::FLATTEN: return "FLATTEN";
    case RewriteProofStatus::DSL: return "DSL";
    case RewriteProofStatus::DSL_FIXED_POINT: return "DSL_FIXED_POINT";
    case RewriteProofStatus::THEORY_REWRITE: return "THEORY_REWRITE";
    default: Unreachable();
  }
}

std::ostream& operator<<(std::ostream& out, RewriteProofStatus s)
{
  out << toString(s);
  return out;
}

}  // namespace rewriter
}  // namespace cvc5::internal
