/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
const char* toString(DslProofRule drule)
{
  switch (drule)
  {
    case DslProofRule::FAIL: return "FAIL";
    case DslProofRule::REFL: return "REFL";
    case DslProofRule::EVAL:
      return "EVAL";
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
