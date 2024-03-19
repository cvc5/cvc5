/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Leni Aniva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated rewrites
 */

#include "expr/node.h"
#include "expr/node_manager.h"
#include "proof/proof_checker.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrites.h"
#include "theory/builtin/generic_op.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

// clang-format off
${decl_individual_rewrites}$
// clang-format on

void addRules(RewriteDb& db)
{
  // Calls to individual rewrites
  // clang-format off
  ${call_individual_rewrites}$
  // clang-format on
}

bool isInternalDslProofRule(DslProofRule drule)
{
  return drule == DslProofRule::FAIL || drule == DslProofRule::REFL
         || drule == DslProofRule::EVAL || drule == DslProofRule::TRANS
         || drule == DslProofRule::CONG || drule == DslProofRule::CONG_EVAL
         || drule == DslProofRule::TRUE_ELIM
         || drule == DslProofRule::TRUE_INTRO
         || drule == DslProofRule::ARITH_POLY_NORM
         || drule == DslProofRule::ACI_NORM;
}

const char* toString(DslProofRule drule)
{
  switch (drule)
  {
    case DslProofRule::FAIL: return "FAIL";
    case DslProofRule::REFL: return "REFL";
    case DslProofRule::EVAL: return "EVAL";
    case DslProofRule::TRANS: return "TRANS";
    case DslProofRule::CONG: return "CONG";
    case DslProofRule::CONG_EVAL: return "CONG_EVAL";
    case DslProofRule::TRUE_ELIM: return "TRUE_ELIM";
    case DslProofRule::TRUE_INTRO: return "TRUE_INTRO";
    case DslProofRule::ARITH_POLY_NORM: return "ARITH_POLY_NORM";
    case DslProofRule::ACI_NORM: return "ACI_NORM";
      // clang-format off
${printer}$
    default : Unreachable();
      // clang-format on
  }
}

std::ostream& operator<<(std::ostream& out, DslProofRule drule)
{
  out << toString(drule);
  return out;
}

Node mkDslProofRuleNode(DslProofRule i)
{
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(i)));
}

bool getDslProofRule(TNode n, DslProofRule& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<DslProofRule>(index);
  return true;
}

}  // namespace rewriter
}  // namespace cvc5::internal
