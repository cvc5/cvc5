/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated rewrites
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__REWRITES__H
#define CVC5__REWRITER__REWRITES__H

#include "cvc5/cvc5_proof_rule.h"
#include "expr/node.h"

namespace cvc5::internal {

namespace rewriter {

class RewriteDb;

/**
 * The body of this method is auto-generated. This populates the provided
 * rewrite rule database with rules based on the compilation of the DSL
 * rewrite rule files.
 */
void addRules(RewriteDb& db);

/** Make node from proof rewrite rule */
Node mkRewriteRuleNode(ProofRewriteRule rule);

/** get a proof rewrite rule from a node, return false if we fail */
bool getRewriteRule(TNode n, ProofRewriteRule& rule);

}  // namespace rewriter
}  // namespace cvc5::internal

#endif
