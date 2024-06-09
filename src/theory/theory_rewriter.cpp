/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {

std::ostream& operator<<(std::ostream& os, TheoryRewriteCtx trc)
{
  switch (trc)
  {
    case TheoryRewriteCtx::PRE_DSL: return os << "PRE_DSL";
    case TheoryRewriteCtx::DSL_SUBCALL: return os << "DSL_SUBCALL";
    case TheoryRewriteCtx::POST_DSL: return os << "POST_DSL";
  }
  Unreachable();
  return os;
}

std::ostream& operator<<(std::ostream& os, RewriteStatus rs)
{
  switch (rs)
  {
    case RewriteStatus::REWRITE_DONE:       return os << "DONE";
    case RewriteStatus::REWRITE_AGAIN:      return os << "AGAIN";
    case RewriteStatus::REWRITE_AGAIN_FULL: return os << "AGAIN_FULL";
  }
  Unreachable();
  return os;
}

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

Node TheoryRewriter::rewriteViaRule(ProofRewriteRule pr, const Node& n)
{
  return n;
}

ProofRewriteRule TheoryRewriter::findRule(const Node& a,
                                          const Node& b,
                                          TheoryRewriteCtx ctx)
{
  std::unordered_set<ProofRewriteRule>& rules = d_pfTheoryRewrites[ctx];
  for (ProofRewriteRule r : rules)
  {
    if (rewriteViaRule(r, a) == b)
    {
      return r;
    }
  }
  return ProofRewriteRule::NONE;
}

void TheoryRewriter::registerProofRewriteRule(ProofRewriteRule id,
                                              TheoryRewriteCtx ctx)
{
  std::unordered_set<ProofRewriteRule>& rules = d_pfTheoryRewrites[ctx];
  rules.insert(id);
  // theory rewrites marked DSL_SUBCALL are also tried at PRE_DSL effort.
  if (ctx == TheoryRewriteCtx::DSL_SUBCALL)
  {
    d_pfTheoryRewrites[TheoryRewriteCtx::PRE_DSL].insert(id);
  }
}

NodeManager* TheoryRewriter::nodeManager() const { return d_nm; }

}  // namespace theory
}  // namespace cvc5::internal
