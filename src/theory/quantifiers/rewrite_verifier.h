/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for finding unsoundness in the rewriter
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__REWRITE_VERIFIER_H
#define CVC5__THEORY__QUANTIFIERS__REWRITE_VERIFIER_H

#include "expr/node.h"
#include "theory/quantifiers/expr_miner.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * RewriteVerifier, which tests the rewritten form of terms provided to addTerm.
 */
class RewriteVerifier : public ExprMiner
{
 public:
  RewriteVerifier(Env& env);
  ~RewriteVerifier() {}
  /**
   * Add term to this module, which may add an equality of the form
   * (= n Rewriter::rewrite(n)) to rewrites if we discover the rewrite is
   * unsound.
   */
  bool addTerm(Node n, std::vector<Node>& rewrites) override;

 private:
  /** check equivalent
   *
   * Check whether bv and bvr are equivalent on all sample points, print
   * an error if not. Used with --sygus-rr-verify.
   *
   * @param bv The original term
   * @param bvr The rewritten form of bvr
   * @param out The output stream to write if the rewrite was unsound.
   */
  bool checkEquivalent(Node bv, Node bvr, std::ostream* out = nullptr);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__REWRITE_VERIFIER_H */
