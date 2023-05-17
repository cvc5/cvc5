/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter of builtin theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H
#define CVC5__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

class TheoryBuiltinRewriter : public TheoryRewriter
{
  static Node blastDistinct(TNode node);

 public:

  RewriteResponse postRewrite(TNode node) override;

  RewriteResponse preRewrite(TNode node) override { return doRewrite(node); }

 public:
  /**
   * The default rewriter for rewrites that occur at both pre and post rewrite.
   */
  static RewriteResponse doRewrite(TNode node);
  /**
   * Main entry point for rewriting terms of the form (witness ((x T)) (P x)).
   * Returns the rewritten form of node.
   */
  static Node rewriteWitness(TNode node);
  /**
   * Main entry point for rewriting APPLY_INDEXED_SYMBOLIC terms.
   */
  static Node rewriteApplyIndexedSymbolic(TNode node);
}; /* class TheoryBuiltinRewriter */

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H */
