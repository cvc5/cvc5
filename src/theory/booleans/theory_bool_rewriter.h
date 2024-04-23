/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

#ifndef CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H
#define CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H

#include "theory/theory_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace booleans {

class TheoryBoolRewriter : public TheoryRewriter
{
 public:
  TheoryBoolRewriter(NodeManager* nm);
  RewriteResponse preRewrite(TNode node) override;
  RewriteResponse postRewrite(TNode node) override;

 protected:
  /**
   * Helper method which performs flattening.
   *
   * @param n The node to flatten
   * @param trivialNode The trivial node, e.g. false if n is an AND application
   * @param skipNode The skip node, e.g. true if n is an AND application
   * @return The flattened node.
   */
  RewriteResponse flattenNode(TNode n, TNode trivialNode, TNode skipNode);
  /**
   * Helper method for making a negation
   *
   * @param n The node to negate
   * @return The negation of n.
   */
  Node makeNegation(TNode n);
  /** Common constants */
  Node d_true;
  Node d_false;
};

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BOOLEANS__THEORY_BOOL_REWRITER_H */
