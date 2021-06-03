/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The TheoryRewriter class.
 *
 * The interface that theory rewriters implement.
 */

#include "theory/theory_rewriter.h"

namespace cvc5 {
namespace theory {

TrustRewriteResponse::TrustRewriteResponse(RewriteStatus status,
                                           Node n,
                                           Node nr,
                                           ProofGenerator* pg)
    : d_status(status)
{
  // we always make non-null, regardless of whether n = nr
  d_node = TrustNode::mkTrustRewrite(n, nr, pg);
}

TrustRewriteResponse TheoryRewriter::postRewriteWithProof(TNode node)
{
  RewriteResponse response = postRewrite(node);
  // by default, we return a trust rewrite response with no proof generator
  return TrustRewriteResponse(
      response.d_status, node, response.d_node, nullptr);
}

TrustRewriteResponse TheoryRewriter::preRewriteWithProof(TNode node)
{
  RewriteResponse response = preRewrite(node);
  // by default, we return a trust rewrite response with no proof generator
  return TrustRewriteResponse(
      response.d_status, node, response.d_node, nullptr);
}

Node TheoryRewriter::rewriteEqualityExt(Node node) { return node; }

TrustNode TheoryRewriter::rewriteEqualityExtWithProof(Node node)
{
  Node nodeRew = rewriteEqualityExt(node);
  if (nodeRew != node)
  {
    // by default, we return a trust rewrite response with no proof generator
    return TrustNode::mkTrustRewrite(node, nodeRew, nullptr);
  }
  // no rewrite
  return TrustNode::null();
}

TrustNode TheoryRewriter::expandDefinition(Node node)
{
  // no expansion
  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5
