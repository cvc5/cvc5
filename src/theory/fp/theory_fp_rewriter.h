/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__THEORY_FP_REWRITER_H
#define CVC5__THEORY__FP__THEORY_FP_REWRITER_H

#include "theory/fp/fp_expand_defs.h"
#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace fp {

typedef RewriteResponse (*RewriteFunction)(NodeManager* nm, TNode, bool);

class TheoryFpRewriter : public TheoryRewriter
{
 public:
  TheoryFpRewriter(NodeManager* nm, context::UserContext* u, bool fpExp);

  RewriteResponse preRewrite(TNode node) override;
  RewriteResponse postRewrite(TNode node) override;

  /**
   * Rewrite an equality, in case special handling is required.
   */
  Node rewriteEquality(TNode equality)
  {
    // often this will suffice
    return postRewrite(equality).d_node;
  }
  /** Expand definitions in node */
  Node expandDefinition(Node node) override;

 protected:
  /** TODO: document (projects issue #265) */
  RewriteFunction d_preRewriteTable[static_cast<uint32_t>(Kind::LAST_KIND)];
  RewriteFunction d_postRewriteTable[static_cast<uint32_t>(Kind::LAST_KIND)];
  RewriteFunction d_constantFoldTable[static_cast<uint32_t>(Kind::LAST_KIND)];
  /** The expand definitions module. */
  FpExpandDefs d_fpExpDef;
  /** True if --fp-exp is enabled */
  bool d_fpExpEnabled;
}; /* class TheoryFpRewriter */

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FP__THEORY_FP_REWRITER_H */
