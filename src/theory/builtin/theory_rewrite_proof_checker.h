/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Builtin proof checker utility for THEORY_REWRITE.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__THEORY_REWRITE_PROOF_CHECKER_H
#define CVC5__THEORY__BUILTIN__THEORY_REWRITE_PROOF_CHECKER_H

#include <cvc5/cvc5_proof_rule.h>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

/** A checker for builtin proofs */
class TheoryRewriteProofChecker
{
 public:
  /** Constructor. */
  TheoryRewriteProofChecker(NodeManager* nm);
  /**
   * Check. Returns the rewritten term for ProofRule::THEORY_REWRITE for the
   * identifier id and argument term lhs, or Node::null() if the input is
   * invalid.
   *
   * @param id The proof rewrite rule.
   * @param lhs The term to rewrite.
   * @return The right hand side of THEORY_REWRITE for the identifier and term.
   */
  Node checkRewrite(ProofRewriteRule id, const Node& lhs);

 private:
  /** Pointer to the node manager */
  NodeManager* d_nm;
};

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__PROOF_CHECKER_H */
