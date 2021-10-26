/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated rewrites
 */

#include "expr/node.h"
#include "expr/node_manager.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrites.h"
#include "util/string.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace rewriter {

void addRules(RewriteDb& db)
{
  NodeManager* nm = NodeManager::currentNM();

  // Variables
  // clang-format off
${decls}$

  // Definitions
${defns}$

  // Rules
${rules}$
  // clang-format on
}
bool isInternalDslPfRule(DslPfRule drule)
{
  return drule == DslPfRule::FAIL || drule == DslPfRule::REFL
         || drule == DslPfRule::EVAL || drule == DslPfRule::TRANS
         || drule == DslPfRule::CONG || drule == DslPfRule::TRUE_ELIM
         || drule == DslPfRule::TRUE_INTRO
         || drule == DslPfRule::ARITH_POLY_NORM;
}
const char* toString(DslPfRule drule)
{
  switch (drule)
  {
    case DslPfRule::FAIL: return "FAIL";
    case DslPfRule::REFL: return "REFL";
    case DslPfRule::EVAL: return "EVAL";
    case DslPfRule::TRANS: return "TRANS";
    case DslPfRule::CONG: return "CONG";
    case DslPfRule::TRUE_ELIM: return "TRUE_ELIM";
    case DslPfRule::TRUE_INTRO: return "TRUE_INTRO";
    case DslPfRule::ARITH_POLY_NORM:
      return "ARITH_POLY_NORM";
      // clang-format off
${printer}$
    default : Unreachable();
      // clang-format on
  }
}

std::ostream& operator<<(std::ostream& out, DslPfRule drule)
{
  out << toString(drule);
  return out;
}

}  // namespace rewriter
}  // namespace cvc5
