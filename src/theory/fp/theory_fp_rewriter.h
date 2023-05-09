/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Martin Brain, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

typedef RewriteResponse (*RewriteFunction) (TNode, bool);

class TheoryFpRewriter : public TheoryRewriter
{
 public:
  TheoryFpRewriter(context::UserContext* u);

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
  TrustNode expandDefinition(Node node) override;

 protected:
  /** TODO: document (projects issue #265) */
  RewriteFunction d_preRewriteTable[kind::LAST_KIND];
  RewriteFunction d_postRewriteTable[kind::LAST_KIND];
  RewriteFunction d_constantFoldTable[kind::LAST_KIND];
  /** The expand definitions module. */
  FpExpandDefs d_fpExpDef;
}; /* class TheoryFpRewriter */

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FP__THEORY_FP_REWRITER_H */
