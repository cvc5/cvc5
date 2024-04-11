/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr
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

#include "cvc5_public.h"

#ifndef CVC5__REWRITER__REWRITES__H
#define CVC5__REWRITER__REWRITES__H

#include "expr/node.h"

namespace cvc5::internal {
namespace rewriter {

class RewriteDb;

/**
 * Identifiers for DSL proof rules
 */
enum class DslProofRule : uint32_t
{
  NONE = 0,
  // Generated rule ids
  // clang-format off
  ${rule_ids}$
  // clang-format on
};

/**
 * The body of this method is auto-generated. This populates the provided
 * rewrite rule database with rules based on the compilation of the DSL
 * rewrite rule files.
 */
void addRules(RewriteDb& db);

/**
 * Converts a DSL proof rule to a string.
 * @param drule The DSL proof rule
 * @return The name of the DSL proof rule
 */
const char* toString(DslProofRule drule);
/**
 * Writes a DSL proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param drule The DSL proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, DslProofRule drule);

/** Make node from DSL proof rule id */
Node mkDslProofRuleNode(DslProofRule i);

/** get a DSL proof rule identifier from a node, return false if we fail */
bool getDslProofRule(TNode n, DslProofRule& i);

}  // namespace rewriter
}  // namespace cvc5::internal

#endif
