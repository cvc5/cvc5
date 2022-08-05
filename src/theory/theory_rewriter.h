/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The TheoryRewriter class.
 *
 * The interface that theory rewriters implement.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_REWRITER_H
#define CVC5__THEORY__THEORY_REWRITER_H

#include "expr/node.h"
#include "proof/trust_node.h"

namespace cvc5::internal {
namespace theory {

class Rewriter;

/**
 * Theory rewriters signal whether more rewriting is needed (or not)
 * by using a member of this enumeration.  See RewriteResponse, below.
 */
enum RewriteStatus
{
  /**
   * The node is fully rewritten (no more rewrites apply for the original
   * kind). If the rewrite changes the kind, the rewriter will apply another
   * round of rewrites.
   */
  REWRITE_DONE,
  /** The node may be rewritten further */
  REWRITE_AGAIN,
  /** Subnodes of the node may be rewritten further */
  REWRITE_AGAIN_FULL
}; /* enum RewriteStatus */

/** Print a RewriteStatus to an output stream */
std::ostream& operator<<(std::ostream& os, RewriteStatus rs);

/**
 * Instances of this class serve as response codes from
 * TheoryRewriter::preRewrite() and TheoryRewriter::postRewrite(). The response
 * consists of the rewritten node as well as a status that indicates whether
 * more rewriting is needed or not.
 */
struct RewriteResponse
{
  const RewriteStatus d_status;
  const Node d_node;
  RewriteResponse(RewriteStatus status, Node n) : d_status(status), d_node(n) {}
}; /* struct RewriteResponse */

/** Same as above, with trust node instead of node. */
struct TrustRewriteResponse
{
  TrustRewriteResponse(RewriteStatus status,
                       Node n,
                       Node nr,
                       ProofGenerator* pg);
  /** The status of the rewrite */
  const RewriteStatus d_status;
  /**
   * The trust node corresponding to the rewrite.
   */
  TrustNode d_node;
};

/**
 * The interface that a theory rewriter has to implement.
 *
 * Note: A theory rewriter is expected to handle all kinds of a theory, even
 * the ones that are removed by preprocessing since it may be
 * called on terms before the definitions have been expanded.
 */
class TheoryRewriter
{
 public:
  virtual ~TheoryRewriter() = default;

  /**
   * Registers the rewrites of a given theory with the rewriter.
   *
   * @param rewriter The rewriter to register the rewrites with.
   */
  virtual void registerRewrites(Rewriter* rewriter) {}

  /**
   * Performs a pre-rewrite step.
   *
   * @param node The node to rewrite
   */
  virtual RewriteResponse postRewrite(TNode node) = 0;

  /**
   * Performs a pre-rewrite step, with proofs.
   *
   * @param node The node to rewrite
   */
  virtual TrustRewriteResponse postRewriteWithProof(TNode node);

  /**
   * Performs a post-rewrite step.
   *
   * @param node The node to rewrite
   */
  virtual RewriteResponse preRewrite(TNode node) = 0;

  /**
   * Performs a pre-rewrite step, with proofs.
   *
   * @param node The node to rewrite
   */
  virtual TrustRewriteResponse preRewriteWithProof(TNode node);

  /** rewrite equality extended
   *
   * This method returns a formula that is equivalent to the equality between
   * two terms s = t, given by node.
   *
   * Specifically, this method performs rewrites whose conclusion is not
   * necessarily one of { s = t, t = s, true, false }. This is in constrast
   * to postRewrite and preRewrite above, where the rewritten form of an
   * equality must be one of these.
   *
   * @param node The node to rewrite
   */
  virtual Node rewriteEqualityExt(Node node);

  /** rewrite equality extended, with proofs
   *
   * @param node The node to rewrite
   * @return A trust node of kind TrustNodeKind::REWRITE, or the null trust
   * node if no rewrites are applied.
   */
  virtual TrustNode rewriteEqualityExtWithProof(Node node);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__THEORY_REWRITER_H */
